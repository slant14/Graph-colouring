# Exact check of the metric gadget instances produced by run_layout.jl.
#
# For the instances with |V'| = nk <= 15 we recompute the naive and the optimized
# line orders, map G'_k with UnitDiskMapping.jl (Weighted mode), attach source
# weights w in [0,1] to the vertices of G'_k (map_weights), solve MWIS on the
# resulting weighted unit-disk graph exactly, and check the offset identity
#
#     MWIS(A, mapped w) = MWIS(G'_k, w) + overhead
#
# for w = 1/2 everywhere (so the right side is alpha(G'_k)/2 + overhead) and for
# two random weight vectors.  MWIS on A is computed by an exact frontier dynamic
# program that sweeps the lattice column by column (memory is bounded by the
# number of independent configurations of the atoms in two adjacent columns);
# MWIS on G'_k by exhaustive enumeration.  Run:  julia benchmarks/verify_layout.jl

using UnitDiskMapping, Graphs, Random

include(joinpath(@__DIR__, "layout_common.jl"))

# exact MWIS of a weighted unit-disk graph on the lattice, by frontier DP
function mwis_lattice(locs, w, radius)
    n = length(locs)
    order = sortperm(locs; by = l -> (l[2], l[1]))         # column-major sweep
    pos = invperm(order)
    adj(a, b) = sum(abs2, locs[a] .- locs[b]) <= radius^2
    nbrs = [[b for b in 1:n if b != a && adj(a, b)] for a in 1:n]
    last_use = [maximum((pos[b] for b in nbrs[a]); init = pos[a]) for a in 1:n]
    frontier = Int[]                                        # vertex ids
    states = Dict{UInt128,Float64}(UInt128(0) => 0.0)       # bitmask over frontier
    for (t, v) in enumerate(order)
        F2 = [u for u in frontier if last_use[u] > t]
        last_use[v] > t && push!(F2, v)
        length(F2) <= 128 || error("frontier too wide")
        idx = Dict(u => i for (i, u) in enumerate(F2))
        vbits = [i for (i, u) in enumerate(frontier) if u in nbrs[v]]
        new = Dict{UInt128,Float64}()
        for (s, W) in states
            s2 = UInt128(0)
            for (i, u) in enumerate(frontier)
                if (s >> (i - 1)) & 1 == 1 && haskey(idx, u)
                    s2 |= UInt128(1) << (idx[u] - 1)
                end
            end
            new[s2] = max(get(new, s2, -Inf), W)            # v excluded
            if all(i -> (s >> (i - 1)) & 1 == 0, vbits)     # v included
                s3 = haskey(idx, v) ? s2 | (UInt128(1) << (idx[v] - 1)) : s2
                new[s3] = max(get(new, s3, -Inf), W + w[v])
            end
        end
        frontier, states = F2, new
    end
    maximum(values(states))
end

function mwis_brute(g, w)
    best = 0.0
    for mask in 0:(1 << nv(g)) - 1
        ok = all(e -> !((mask >> (src(e) - 1)) & 1 == 1 && (mask >> (dst(e) - 1)) & 1 == 1), edges(g))
        ok && (best = max(best, sum(w[i] for i in 1:nv(g) if (mask >> (i - 1)) & 1 == 1; init = 0.0)))
    end
    best
end

function check(name, k, g, label, order, rng)
    res = map_graph(Weighted(), g; vertex_order = order)
    locs = [x.loc for x in res.grid_graph.nodes]
    ok = true
    for (wlabel, w) in (("w=1/2", fill(0.5, nv(g))), ("random", rand(rng, nv(g))), ("random", rand(rng, nv(g))))
        mw = map_weights(res, w)
        lhs = mwis_lattice(locs, Float64.(mw), res.grid_graph.radius)
        rhs = mwis_brute(g, w) + res.mis_overhead
        good = isapprox(lhs, rhs; atol = 1e-8)
        ok &= good
        println(rpad("$name k=$k $label", 22), rpad(wlabel, 8), " atoms=", lpad(length(locs), 4),
                "  MWIS(A)=", round(lhs, digits = 6), "  MWIS(G')+overhead=", round(rhs, digits = 6),
                good ? "  OK" : "  FAIL")
        flush(stdout)
    end
    ok
end

function main()
    rng = MersenneTwister(20260901)
    allok = true
    for (name, n, es, k) in SUITE
        n * k <= 15 || continue
        g = color_choice(n, es, k)
        allok &= check(name, k, g, "naive", collect(1:nv(g)), rng)
        allok &= check(name, k, g, "ours", repair(g, fiedler_order(g)), rng)
    end
    println(allok ? "all checks passed" : "SOME CHECKS FAILED")
    allok || exit(1)
end

main()
