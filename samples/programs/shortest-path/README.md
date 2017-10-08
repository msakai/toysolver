# shortest-path

Sample problem of `ToySolver.Graph.ShortestPath` module.

It takes `.gr` file and list of source vertexes as command line argument.

Some instances are available at <http://www.diag.uniroma1.it/challenge9/download.shtml>,
and `.gr` file format specification is available at <http://www.diag.uniroma1.it/challenge9/format.shtml#graph>.

If `--method` argument specifies `dijkstra` or `bellman-ford`, shortest-paths
from any of those source vertexes to all reachable vertexes are computed.

If `--method` argument specifies `floyed-warshall`, those source vertexes
are ignored, and shortest-path between all rearchable vertex pairs are computed.
