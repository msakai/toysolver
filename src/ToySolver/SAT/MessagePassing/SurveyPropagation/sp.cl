/* -*- mode: c -*- */

#ifdef USE_CONSTANT_BUFFER
#define CONSTANT __constant
#else
#define CONSTANT __global
#endif

typedef float logfloat;
typedef float2 logfloat2;

static inline logfloat comp(logfloat x) {
  return log1p(fmax(-1.0f, -exp(x)));
}

__kernel void
update_edge_prob(
    int n_vars,
    CONSTANT int *var_offset,         // int[n_vars]
    CONSTANT int *var_degree,         // int[n_vars]
    CONSTANT int *var_edges,          // int[M]
    CONSTANT float *var_edges_weight, // float[M]
    __global logfloat2 *var_edges_buf,// logfloat2[M]
    __global logfloat *edge_survey,   // logfloat[n_edges]
    __global logfloat *edge_prob_u    // logfloat[n_edges]
    )
{
    int global_size = get_global_size(0);
    for (int i = get_global_id(0); i < n_vars; i += global_size) {
        int offset = var_offset[i];
        int degree = var_degree[i];

        logfloat val1_pre = log(1.0);
        logfloat val2_pre = log(1.0);
        for (int j = 0; j < degree; j++) {
            var_edges_buf[offset+j] = (float2)(val1_pre, val2_pre);

            int tmp = var_edges[offset+j];
            int e = tmp >> 1;
            bool polarity = tmp & 1;
            logfloat eta_ai = edge_survey[e];
            logfloat w = var_edges_weight[offset+j];

            if (polarity) {
              val1_pre += comp(eta_ai) * w;
            } else {
              val2_pre += comp(eta_ai) * w;
            }
        }

        logfloat val1_post = log(1.0);
        logfloat val2_post = log(1.0);
        for (int j = degree - 1; j >= 0; j--) {
            int tmp = var_edges[offset+j];
            int e = tmp >> 1;
            bool polarity = tmp & 1;
            logfloat eta_ai = edge_survey[e];
            float w = var_edges_weight[offset+j];

            logfloat2 pre = var_edges_buf[offset+j];
            logfloat val1 = pre.x + val1_post; // probability that other edges do not depends on v=1.
            logfloat val2 = pre.y + val2_post; // probability that other edges do not depends on v=0.
            logfloat pi_0 = val1 + val2; // Π^0_{i→a}
            logfloat pi_u; // Π^u_{i→a}
            logfloat pi_s; // Π^s_{i→a}
            if (polarity) {
                pi_u = comp(val2) + val1;
                pi_s = comp(val1) + val2;
                val1_post += comp(eta_ai) * w;
            } else {
                pi_u = comp(val1) + val2;
                pi_s = comp(val2) + val1;
                val2_post += comp(eta_ai) * w;
            }
            float psum = exp(pi_0) + exp(pi_u) + exp(pi_s);
            if (psum > 0) {
                edge_prob_u[e] = pi_u - log(psum);
            } else {
                edge_prob_u[e] = log(0.0); // is that ok?
            }
        }
    }
}


__kernel void
update_edge_survey(
   int n_clauses,
   CONSTANT int *clause_offset,     // int[n_clauses]
   CONSTANT int *clause_degree,     // int[n_clauses]
   __global logfloat *edge_survey,  // logfloat[n_edges]
   __global logfloat *edge_prob_u,  // logfloat[n_edges]
   __global logfloat *edge_buf,     // logfloat[n_edges]
   __global float *group_max_delta, // float[get_num_groups(0)]
   __local float *reduce_buf        // float[get_local_size(0)]
   )
{
    float max_delta = 0;

    int global_size = get_global_size(0);
    for (int a = get_global_id(0); a < n_clauses; a += global_size) {
        int len = clause_degree[a];
        int offset = clause_offset[a];

        logfloat pre = log(1.0);
        for (int j = 0; j < len; j++) {
            int e = offset+j;
            edge_buf[e] = pre;
            pre += edge_prob_u[e];
        }

        logfloat post = log(1.0);
        for (int j = len-1; j >=0; j--) {
            int e = offset+j;
            logfloat pre = edge_buf[e];
            logfloat eta_ai_orig = edge_survey[e];
            logfloat eta_ai_new  = pre + post;
            edge_survey[e] = eta_ai_new;
            max_delta = fmax(max_delta, fabs(exp(eta_ai_new) - exp(eta_ai_orig)));
            post += edge_prob_u[e];
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
    CONSTANT int *var_offset,            // int[n_vars]
    CONSTANT int *var_degree,            // int[n_vars]
    __global logfloat2 *var_prob,        // logfloat2[n_vars]
    CONSTANT int *var_edges,             // int[M]
    CONSTANT logfloat *var_edges_weight, // logfloat[M]
    __global logfloat *edge_survey       // logfloat[E]
    )
{
    int global_size = get_global_size(0);

    for (int i = get_global_id(0); i < n_vars; i += global_size) {
        int offset = var_offset[i];
        int degree = var_degree[i];

        logfloat val1 = log(1.0);
        logfloat val2 = log(1.0);
        for (int j = 0; j < degree; j++) {
            int tmp = var_edges[offset+j];
            int e = tmp >> 1;
            bool polarity = tmp & 1;
            float eta_ai = edge_survey[e];
            float w = var_edges_weight[offset+j];

            if (polarity) {
              val1 += comp(eta_ai) * w;
            } else {
              val2 += comp(eta_ai) * w;
            }
        }

        float p0 = val1 + val2;       // \^{Π}^{0}_i
        float pp = comp(val1) + val2; // \^{Π}^{+}_i
        float pn = comp(val2) + val1; // \^{Π}^{-}_i
        float wp = pp - log(exp(pp) + exp(pn) + exp(p0)); // W^{(+)}_i
        float wn = pn - log(exp(pp) + exp(pn) + exp(p0)); // W^{(-)}_i
        var_prob[i] = (float2)(wp, wn);
    }
}
