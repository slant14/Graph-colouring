# Shared definitions for run_layout.jl and verify_layout.jl: the benchmark
# instances, the Stage-1 colour-choice graph, the metrics of one UnitDiskMapping
# layout, and the line-order optimizer (H4 spectral order + H5-style repair).

using UnitDiskMapping, Graphs, LinearAlgebra

# ── instances (same vertex labelling as the Python benchmarks) ───────────────
cyc(n) = [(i, i % n + 1) for i in 1:n]
pth(n) = [(i, i + 1) for i in 1:n-1]
kn(n) = [(i, j) for i in 1:n for j in i+1:n]
petersen() = vcat([(i, i % 5 + 1) for i in 1:5],                  # outer C5
                  [(5 + i, 5 + (i + 1) % 5 + 1) for i in 1:5],    # pentagram
                  [(i, 5 + i) for i in 1:5])                      # spokes
# networkx.mycielski_graph(m): Mycielskian of P2 iterated m-2 times
function mycielski(m)
    n, E = 2, [(1, 2)]
    for _ in 1:m-2
        E2 = copy(E)
        for (u, v) in E
            push!(E2, (u, v + n)); push!(E2, (u + n, v))
        end
        for u in 1:n
            push!(E2, (u + n, 2n + 1))
        end
        n, E = 2n + 1, E2
    end
    n, E
end

const SUITE = [
    ("K2", 2, [(1, 2)], 2),
    ("P4", 4, pth(4), 2),
    ("C4", 4, cyc(4), 3),
    ("C5", 5, cyc(5), 3),
    ("K4", 4, kn(4), 4),
    ("Petersen", 10, petersen(), 3),
    ("myciel3", mycielski(4)..., 4),
]

function color_choice(n, es, k)
    g = SimpleGraph(n * k)
    slot(v, c) = (v - 1) * k + c
    for v in 1:n, a in 1:k, b in a+1:k
        add_edge!(g, slot(v, a), slot(v, b))
    end
    for (u, w) in es, c in 1:k
        add_edge!(g, slot(u, c), slot(w, c))
    end
    g
end

# ── metrics of one mapping ───────────────────────────────────────────────────
base(p) = p isa UnitDiskMapping.WeightedGadget ? base(p.gadget) :
          p isa UnitDiskMapping.RotatedGadget  ? base(p.gadget) :
          p isa UnitDiskMapping.ReflectedGadget ? base(p.gadget) : p

function measure(g, order)
    res = map_graph(Weighted(), g; vertex_order = order)
    locs = [n.loc for n in res.grid_graph.nodes]
    rows = maximum(first, locs) - minimum(first, locs) + 1
    cols = maximum(last, locs) - minimum(last, locs) + 1
    pats = [base(t[1]) for t in res.mapping_history]
    xe = count(p -> p isa UnitDiskMapping.Cross{true}, pats)
    xn = count(p -> p isa UnitDiskMapping.Cross{false}, pats)
    (atoms = length(locs), cross = xe + xn, cross_edge = xe, cross_plain = xn,
     rows = rows, cols = cols, overhead = res.mis_overhead)
end

function fiedler_order(g)
    L = Matrix{Float64}(laplacian_matrix(g))
    F = eigen(Symmetric(L))
    sortperm(F.vectors[:, 2])
end

# H5-style repair over line orders: integer potential = atom count, accept a swap
# only on strict decrease; at most N^2 swaps are ever accepted.
function repair(g, order)
    best = measure(g, order).atoms
    improved = true
    while improved
        improved = false
        for i in 1:length(order)-1
            cand = copy(order)
            cand[i], cand[i+1] = cand[i+1], cand[i]
            a = measure(g, cand).atoms
            if a < best
                best, order, improved = a, cand, true
            end
        end
    end
    order
end
