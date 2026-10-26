# Export the metric gadget instance of the paper's worked example (C4, k = 3,
# optimized line order) as TikZ coordinates for panel (d) of Figure "C4 end to
# end".  Run:  julia benchmarks/export_c4_layout.jl > benchmarks/results/c4_layout.tex

using UnitDiskMapping, Graphs

include(joinpath(@__DIR__, "layout_common.jl"))

g = color_choice(4, cyc(4), 3)
res = map_graph(Weighted(), g; vertex_order = repair(g, fiedler_order(g)))
nodes = res.grid_graph.nodes
centers = Set(UnitDiskMapping.trace_centers(res))
r0 = minimum(n.loc[1] for n in nodes); c0 = minimum(n.loc[2] for n in nodes)
println("% C4, k=3: $(length(nodes)) atoms, overhead $(res.mis_overhead); (col,row) in lattice units")
for (cls, pick) in (("lg", n -> n.loc in centers),
                    ("hv", n -> !(n.loc in centers) && n.weight > 2),
                    ("lt", n -> !(n.loc in centers) && n.weight <= 2))
    pts = [n for n in nodes if pick(n)]
    println("% $cls: $(length(pts)) atoms")
    println("\\foreach \\x/\\y in {", join(["$(n.loc[2]-c0)/$(-(n.loc[1]-r0))" for n in pts], ","), "}{\\node[$cls] at (\\x*\\u,\\y*\\u) {};}")
end
