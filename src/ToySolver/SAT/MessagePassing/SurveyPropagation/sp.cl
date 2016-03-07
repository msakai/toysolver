/* -*- mode: c -*- */

__kernel void
update_edge_prob(
    int n_vars,
    __constant int *var_offset,           // int[n_vars]
    __constant int *var_degree,           // int[n_vars]
    __constant int *var_edges,            // int[M]
    __constant float *var_edges_weight,   // float[M]
    __global float2 *var_edges_buf,       // float2[M]
    __global float *edge_survey,          // float[n_edges]
    __global float *edge_prob_u           // float[n_edges]
    )
{
    int global_size = get_global_size(0);
    for (int i = get_global_id(0); i < n_vars; i += global_size) {
        int offset = var_offset[i];
        int degree = var_degree[i];

        float val1_pre = 1;
        float val2_pre = 1;
        for (int j = 0; j < degree; j++) {
            var_edges_buf[offset+j] = (float2)(val1_pre, val2_pre);

            int tmp = var_edges[offset+j];
            int e = tmp >> 1;
            bool polarity = tmp & 1;
            float eta_ai = edge_survey[e];
            float w = var_edges_weight[offset+j];

            if (polarity) {
              val1_pre *= pow(1 - eta_ai, w);
            } else {
              val2_pre *= pow(1 - eta_ai, w);
            }
        }

        float val1_post = 1;
        float val2_post = 1;
        for (int j = degree - 1; j >= 0; j--) {
            int tmp = var_edges[offset+j];
            int e = tmp >> 1;
            bool polarity = tmp & 1;
            float eta_ai = edge_survey[e];
            float w = var_edges_weight[offset+j];

            float2 pre = var_edges_buf[offset+j];
            float val1 = pre.x * val1_post; // probability that other edges do not depends on v=1.
            float val2 = pre.y * val2_post; // probability that other edges do not depends on v=0.
            float pi_0 = val1 * val2; // Π^0_{i→a}
            float pi_u; // Π^u_{i→a}
            float pi_s; // Π^s_{i→a}
            if (polarity) {
                pi_u = (1 - val2) * val1;
                pi_s = (1 - val1) * val2;
                val1_post *= pow(1 - eta_ai, w);
            } else {
                pi_u = (1 - val1) * val2;
                pi_s = (1 - val2) * val1;
                val2_post *= pow(1 - eta_ai, w);
            }
            float psum = pi_0 + pi_u + pi_s;
            if (psum != 0) {
                edge_prob_u[e] = pi_u / psum;
            } else {
                edge_prob_u[e] = 0; // is that ok?
            }
        }
    }
}


__kernel void
update_edge_survey(
   int n_clauses,
   __constant int *clause_offset,   // int[n_clauses]
   __constant int *clause_degree,   // int[n_clauses]
   __global float *edge_survey,     // float[n_edges]
   __global float *edge_prob_u,     // float[n_edges]
   __global float *edge_buf,        // float[n_edges]
   __global float *group_max_delta, // float[get_num_groups(0)]
   __local float *reduce_buf        // float[get_local_size(0)]
   )
{
    float max_delta = 0;

    int global_size = get_global_size(0);
    for (int a = get_global_id(0); a < n_clauses; a += global_size) {
        int len = clause_degree[a];
        int offset = clause_offset[a];

        float pre = 1;
        for (int j = 0; j < len; j++) {
            int e = offset+j;
            edge_buf[e] = pre;
            pre *= edge_prob_u[e];
        }

        float post = 1;
        for (int j = len-1; j >=0; j--) {
            int e = offset+j;
            float pre = edge_buf[e];
            float eta_ai_orig = edge_survey[e];
            float eta_ai_new  = pre * post;
            edge_survey[e] = eta_ai_new;
            max_delta = fmax(max_delta, fabs(eta_ai_new - eta_ai_orig));
            post *= edge_prob_u[e];
        }
    }

    // reduction
    int local_id = get_local_id(0);
    int local_size = get_local_size(0);
    barrier(CLK_LOCAL_MEM_FENCE);
    reduce_buf[local_id] = max_delta;
    for (int stride = local_size / 2; stride > 0; stride /= 2) {
        barrier(CLK_LOCAL_MEM_FENCE);
        if (local_id < stride) {
            reduce_buf[local_id] = fmax(reduce_buf[local_id], reduce_buf[local_id + stride]);
        }
    }
    if (local_id==0)
        group_max_delta[get_group_id(0)] = reduce_buf[0];
}

__kernel void
compute_var_prob(
    int n_vars,
    __constant int *var_offset,           // int[n_vars]
    __constant int *var_degree,           // int[n_vars]
    __global float2 *var_prob,            // float2[n_vars]
    __constant int *var_edges,            // int[M]
    __constant float *var_edges_weight,   // float[M]
    __global float *edge_survey           // float[E]
    )
{
    int global_size = get_global_size(0);

    for (int i = get_global_id(0); i < n_vars; i += global_size) {
        int offset = var_offset[i];
        int degree = var_degree[i];

        float val1 = 1;
        float val2 = 1;
        for (int j = 0; j < degree; j++) {
            int tmp = var_edges[offset+j];
            int e = tmp >> 1;
            bool polarity = tmp & 1;
            float eta_ai = edge_survey[e];
            float w = var_edges_weight[offset+j];

            if (polarity) {
              val1 *= pow(1 - eta_ai, w);
            } else {
              val2 *= pow(1 - eta_ai, w);
            }
        }

        float p0 = val1 * val2;       // \^{Π}^{0}_i
        float pp = (1 - val1) * val2; // \^{Π}^{+}_i
        float pn = (1 - val2) * val1; // \^{Π}^{-}_i
        float wp = pp / (pp + pn + p0); // W^{(+)}_i
        float wn = pn / (pp + pn + p0); // W^{(-)}_i
        var_prob[i] = (float2)(wp, wn);
    }
}
