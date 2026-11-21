import itertools
import subprocess
from argparse import ArgumentParser

def load_instance(input_file):
    global N1, N2, NR_X_VAR, NR_BASE_VAR
    with open(input_file, "r") as file:
        numbers = [int(i) for line in file for i in line.split("#", 1)[0].split()]

    graphs = []
    for name in ("G1", "G2"):
        if len(numbers) < 2:
            raise ValueError(name+ ": missing 'n m' line")
        n, m = numbers[0], numbers[1]
        edges, numbers = numbers[2:2+2*m], numbers[2+2*m:]
        if len(edges) != 2*m:
            raise ValueError(name + ":announces "+ str(m) +"edges, but file has fewer")
        adj_m = [[False]*n for _ in range(n)]
        for u, v in zip(edges[0::2], edges[1::2]):
            if not (0 <= u < n and 0 <= v < n):
                raise ValueError(name + ":edge " + str(u) + " " +str(v)+ " uses a vertex outside 0.." + str(n-1))
            if u != v:
                adj_m[u][v] = adj_m[v][u] = True
        graphs.append(adj_m)
    if numbers:
        raise ValueError("Unexpected numbers after the second graph")

    N1, N2 = len(graphs[0]), len(graphs[1])
    NR_X_VAR = N1*N2
    NR_BASE_VAR = NR_X_VAR + N1
    return graphs

def s_ID(u):                # s variables are indexed after x variables
    return NR_X_VAR + u + 1

def x_ID(u, a):
    return u*N2 + a + 1

def encode(g1, g2):
    # var x(u,a): vertex u of G1 mapped to a vertex a of G2 
    # var s(u): vertex u of G1 counted towards the size bound
    cnf = []

    # a counted vertes is mapped somewhere
    for u in range(N1):
        cnf.append([-s_ID(u)] + [x_ID(u, a) for a in range(N2)] + [0])
    # a vertex has at most one image
    for u in range(N1):
        for a in range(N2):
            for b in range(a+1, N2):
                cnf.append([-x_ID(u, a), -x_ID(u, b), 0])
    # the map is injective
    for a in range(N2):
        for u in range(N1):
            for v in range(u+1, N1):
                cnf.append([-x_ID(u, a), -x_ID(v, a), 0])
    # edges map to edges, non-edges to non-edges
    # conflict[e] = pairs (a,b), a != b, whose adjacency in G2 differs from e        
    conflict = {e: [(a, b) for a in range(N2) for b in range(N2) if a != b and g2[a][b] != e] for e in {False, True}}
    for u in range(N1):
        for v in range(N1):
            for a, b in conflict[g1[u][v]]:
                cnf.append([-x_ID(u,a), -x_ID(v, b), 0])

    return cnf

def encode_bound(k):
    lits = [-s_ID(u) for u in range(N1)]
    n, K = len(lits), N1 - k

    if K >= n:
        return [], NR_BASE_VAR
    if K==0:
        return [[-l, 0] for l in lits], NR_BASE_VAR

    r = [[NR_BASE_VAR + i*K + j + 1 for j in range(K)] for i in range(n - 1)]
    cnf = [[-lits[0], r[0][0], 0]]
    for j in range(1, K):
        cnf.append([-r[0][j], 0])
    for i in range(1, n-1):
        cnf.append([-lits[i], r[i][0], 0])
        cnf.append([-r[i-1][0], r[i][0], 0])
        for j in range(1, K):
            cnf.append([-lits[i], -r[i-1][j-1], r[i][j], 0])
            cnf.append([-r[i-1][j], r[i][j], 0])
        cnf.append([-lits[i], -r[i-1][K-1], 0])
    cnf.append([-lits[n-1], -r[n-2][K-1], 0])

    return cnf, NR_BASE_VAR + (n-1)*K

def call_solver(fixed_txt, nr_fixed, cnf, nr_vars, output_name, solver_name, ver):
    with open(output_name, "w") as file:
        file.write("p cnf " + str(nr_vars) + " " + str(nr_fixed + len(cnf)) + "\n")
        file.write(fixed_txt)
        for clause in cnf:
            file.write(' '.join(str(lit) for lit in clause) + "\n")

    return subprocess.run(['./' + solver_name, '-model', '-verb=' + str(ver), output_name], stdout=subprocess.PIPE)

def decode(result):
    model = set()
    for line in result.stdout.decode('utf-8').split('\n'):
        if line.startswith("v"):
            model.update(int(v) for v in line.split()[1:] if int(v)>0)
    return [(u, a) for u in range(N1) for a in range(N2) if x_ID(u, a) in model]

def verify(g1, g2, mapping):
    if len({u for u, _ in mapping}) != len(mapping) or len({a for _, a in mapping}) != len(mapping):
        return False
    return all(g1[u][v] == g2[a][b] for (u, a), (v, b) in itertools.combinations(mapping, 2))

def print_result(g1, mapping):
    edges = [((u, a), (v, b)) for (u,a), (v,b) in itertools.combinations(mapping, 2) if g1[u][v]]

    print()
    print("=====================================================================")
    print("[    Largest Commong Induced Subgraph:    " +str(len(mapping)) + " vertices, " + str(len(edges)) + " edges    ]")
    print("=====================================================================")
    print()
    print("vertex mapping   G1 -> G2")
    for u, a in mapping:
        print(" " + str(u) + " -> " + str(a))
    print("edges            G1 -> G2")
    for (u, a), (v, b) in edges:
        print(" " + str(u) + "-" + str(v) + " <-> " +str(a) + "-" + str(b))

if __name__ == "__main__":
    parser = ArgumentParser()

    parser.add_argument(
        "-i",
        "--input",
        default="input.in",
        type=str,
        help=(
            "The instance file: graph G1 then graph G2, each as 'n m' followed by m edges 'u v'."
        ),
    )

    parser.add_argument(
        "-o",
        "--output",
        default="formula.cnf",
        type=str,
        help=(
            "Output file for the DIMACS format (i.e. the CNF formula); holds the last formula solved."
        ),
    )

    parser.add_argument(
        "-s",
        "--solver",
        default="glucose-syrup",
        type=str,
        help=(
            "The SAT solver to be used."
        ),
    )

    parser.add_argument(
        "-v",
        "--verb",
        default=1,
        type=int,
        choices=range(0,2),
        help=(
            "Verbosity of the SAT solver used."
        ),
    )

    args = parser.parse_args()

    g1, g2 = load_instance(args.input)

    fixed = encode(g1, g2)
    fixed_text = "".join(' '.join(str(lit) for lit in clause) + '\n' for clause in fixed)

    best, k = [], 1
    while k <= min(N1, N2):
        cnf, nr_vars = encode_bound(k)
        result = call_solver(fixed_text, len(fixed), cnf, nr_vars, args.output, args.solver, args.verb)
        if result.returncode == 20:     # returncode for SAT is 10, for UNSAT is 20
            print("k >= " + str(k) + ": UNSAT")
            break
        if result.returncode != 10:
            raise SystemExit("solver failed (exit code " + str(result.returncode) + "):\n" + result.stdout.decode('utf-8'))
        best = decode(result)
        if not verify(g1, g2, best) or len(best) < k:
            raise SystemExit("decoded model is not a valid common induced subgraph (encoding bug)")
        print("k >= " + str(k) + ": SAT, found " + str(len(best)) + " vertices")
        k = len(best) + 1

    print_result(g1, best)