# Size of the metric gadget instance for bounded-pathwidth families
# (paper, Proposition "Pathwidth bound" and Figure "scaling").
#
# For G'_k = G □ K_k placed by the *lifted* line order (the vertices of G in an
# order of vertex separation s, each replaced by its k slots), the slot order
# has vertex separation at most k(s+1) - 1, and the copy-line construction of
# Nguyen et al. uses O(|V'| (separation + 1)) atoms; hence O(n k^2 (s+1)) atoms,
# linear in n for fixed k and s.  We map growing paths, cycles, ladders and
# 3 x m grids at k = 3 with UnitDiskMapping.jl (lifted order, and the library's
# own greedy path-decomposition order for comparison), record the vertex
# separation of the lifted order, and contrast with complete graphs (s = n - 1).
#
# Run:  julia benchmarks/run_scaling.jl      Writes results/scaling.csv.

using UnitDiskMapping, Graphs, Printf, Random

include(joinpath(@__DIR__, "layout_common.jl"))

grid_edges(r, c) = vcat([((j - 1) * r + i, (j - 1) * r + i + 1) for j in 1:c for i in 1:r-1],
                        [((j - 1) * r + i, j * r + i) for j in 1:c-1 for i in 1:r])

# vertex separation of an order: max over prefixes of #prefix vertices with a
# neighbour outside the prefix
function vsep(g, order)
    pos = zeros(Int, nv(g)); for (i, v) in enumerate(order); pos[v] = i; end
    best = 0
    for i in 1:length(order)
        c = count(v -> pos[v] <= i && any(w -> pos[w] > i, neighbors(g, v)), vertices(g))
        best = max(best, c)
    end
    best
end

function main()
    Random.seed!(20261002)
    k = 3
    fams = [("path",   n -> (n, pth(n)),            4:4:40),
            ("cycle",  n -> (n, cyc(n)),            4:4:40),
            ("ladder", n -> (n, grid_edges(2, n ÷ 2)), 4:4:40),
            ("grid3",  n -> (n, grid_edges(3, n ÷ 3)), 6:6:36),
            ("complete", n -> (n, kn(n)),           3:1:9)]
    out = joinpath(@__DIR__, "results"); mkpath(out)
    open(joinpath(out, "scaling.csv"), "w") do io
        println(io, "family,n,m,k,nk,vsep_G,vsep_lifted,lifted_bound,atoms_lifted,atoms_greedy,generic_bound,seconds")
        for (fam, make, ns) in fams
            for n in ns
                nn, es = make(n)
                G = SimpleGraph(nn); for (u, v) in es; add_edge!(G, u, v); end
                g = color_choice(nn, es, k)
                t0 = time()
                sG = vsep(G, collect(1:nn))
                lifted = collect(1:nv(g))             # slot (v,c) -> (v-1)k+c
                sL = vsep(g, lifted)
                aL = measure(g, lifted).atoms
                aG = measure(g, Greedy(nrepeat = 10)).atoms
                dt = round(time() - t0, digits = 1)
                @printf("%-8s n=%3d nk=%3d  vs(G)=%2d vs(lifted)=%3d (bound %3d)  atoms lifted=%6d greedy=%6d  4(nk)^2=%7d  (%.1fs)\n",
                        fam, nn, nv(g), sG, sL, k * (sG + 1) - 1, aL, aG, 4 * nv(g)^2, dt)
                println(io, join(Any[fam, nn, length(es), k, nv(g), sG, sL, k * (sG + 1) - 1,
                                     aL, aG, 4 * nv(g)^2, dt], ","))
                flush(io)
            end
        end
    end
    println("wrote $(out)/scaling.csv")
end

main()
