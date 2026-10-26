# Metric layout of the Stage-2 gadget instance (paper, Table "layout optimizer
# against a naive baseline").
#
# For each benchmark instance (G, k) we build the Stage-1 colour-choice graph G'_k
# and map it to a weighted unit-disk instance with UnitDiskMapping.jl, the
# reference implementation of the copy-line / crossing-lattice construction of
# Nguyen et al. (PRX Quantum 4, 010316, 2023).  In that construction the atom
# coordinates are fixed by the lattice once the ORDER of the copy lines is chosen,
# so the order is the layout's discretionary degree of freedom.  We compare:
#
#   naive     the input slot order (v,c) -> (v-1)k+c, i.e. the least clever choice;
#   ours      H4: sort by the Fiedler vector of the Laplacian of G'_k, then an
#             H5-style monotone repair: adjacent transpositions accepted only when
#             the (integer) atom count strictly decreases, so it terminates;
#   ref       UnitDiskMapping's own path-decomposition order (exact branching
#             MinhThiTrick for |V'| <= 16, Greedy(nrepeat=50) above), reported as
#             a reference point.
#
# Every variant uses the same crossing gadgets and the same default simplifier
# rules.  Metrics: atoms |V(A)|; crossing gadgets (with/without edge); bounding
# box of the atoms in lattice sites; whether |V(A)| <= Nmax = 256 (QuEra Aquila).
#
# Run:  julia benchmarks/run_layout.jl      (needs UnitDiskMapping, Graphs)
# Writes benchmarks/results/layout.{csv,json}.

using UnitDiskMapping, Graphs, LinearAlgebra, Random, Printf

const NMAX = 256

include(joinpath(@__DIR__, "layout_common.jl"))

function main()
    Random.seed!(20260901)
    rows = []
    for (name, n, es, k) in SUITE
        g = color_choice(n, es, k)
        N, M = nv(g), ne(g)
        t0 = time()
        naive = measure(g, collect(1:N))
        ours  = measure(g, repair(g, fiedler_order(g)))
        ref   = measure(g, N <= 16 ? MinhThiTrick() : Greedy(nrepeat = 50))
        dt = time() - t0
        r = (; name, n, m = length(es), k, nk = N, edges_gp = M,
               screen = N + 2M, naive, ours, ref, seconds = round(dt, digits = 1))
        push!(rows, r)
        @printf("%-9s k=%d nk=%3d |E'|=%3d screen=%4d | naive %5d atoms %3d x (%2dx%2d) | ours %5d atoms %3d x (%2dx%2d) | ref %5d atoms %3d x (%2dx%2d) | %.1fs\n",
                name, k, N, M, N + 2M,
                naive.atoms, naive.cross, naive.rows, naive.cols,
                ours.atoms, ours.cross, ours.rows, ours.cols,
                ref.atoms, ref.cross, ref.rows, ref.cols, dt)
    end
    out = joinpath(@__DIR__, "results")
    mkpath(out)
    open(joinpath(out, "layout.csv"), "w") do io
        println(io, "name,n,m,k,nk,edges_gp,screen,",
                join(["$(v)_$(f)" for v in ("naive", "ours", "ref")
                      for f in ("atoms", "cross", "cross_edge", "cross_plain", "rows", "cols", "overhead")], ","),
                ",within_nmax_naive,within_nmax_ours,within_nmax_ref,seconds")
        for r in rows
            vals = [getfield(getfield(r, v), f) for v in (:naive, :ours, :ref)
                    for f in (:atoms, :cross, :cross_edge, :cross_plain, :rows, :cols, :overhead)]
            println(io, join(Any[r.name, r.n, r.m, r.k, r.nk, r.edges_gp, r.screen, vals...,
                                 r.naive.atoms <= NMAX, r.ours.atoms <= NMAX, r.ref.atoms <= NMAX,
                                 r.seconds], ","))
        end
    end
    open(joinpath(out, "layout.json"), "w") do io
        j(x::NamedTuple) = "{" * join(["\"$(k)\": " * j(v) for (k, v) in pairs(x)], ", ") * "}"
        j(x::AbstractString) = "\"$x\""
        j(x) = string(x)
        println(io, "[\n  ", join(map(j, rows), ",\n  "), "\n]")
    end
    println("wrote $(out)/layout.csv and layout.json")
end

main()
