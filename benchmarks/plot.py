"""Plots for the benchmark results: a hand-rolled SVG (no matplotlib needed) and
a terminal chart via plotext.  Imported by run_benchmarks.py, or runnable on its
own against an existing results.json:  python benchmarks/plot.py
"""

from __future__ import annotations

import json
import os
from typing import List


# ── SVG grouped bar chart: expected vs actual per (benchmark, k) ─────────────

def _bar_chart_svg(rows: List[dict]) -> str:
    sim = [r for r in rows if r.get("simulated")]
    if not sim:
        return "<svg xmlns='http://www.w3.org/2000/svg'/>"

    W, H = 1000, 460
    L, R, T, B = 60, 20, 60, 110          # margins
    plot_w, plot_h = W - L - R, H - T - B
    ymax = max(max(r["expected"], r["actual"]) for r in sim)
    ymax = max(ymax, 1)
    ng = len(sim)
    slot = plot_w / ng
    bw = slot * 0.30

    def y(v: float) -> float:
        return T + plot_h - (v / ymax) * plot_h

    parts = [
        f"<svg xmlns='http://www.w3.org/2000/svg' width='{W}' height='{H}' "
        f"viewBox='0 0 {W} {H}' font-family='sans-serif'>",
        f"<rect width='100%' height='100%' fill='white'/>",
        f"<text x='{W/2}' y='28' text-anchor='middle' font-size='18' "
        f"font-weight='bold'>Graph colouring: expected (oracle) vs actual "
        f"(Rydberg MWIS sim)</text>",
    ]
    # y grid + axis ticks (integers)
    for v in range(0, ymax + 1):
        yy = y(v)
        parts.append(f"<line x1='{L}' y1='{yy:.1f}' x2='{W-R}' y2='{yy:.1f}' "
                     f"stroke='#eee' stroke-width='1'/>")
        parts.append(f"<text x='{L-8}' y='{yy+4:.1f}' text-anchor='end' "
                     f"font-size='11' fill='#555'>{v}</text>")
    parts.append(f"<line x1='{L}' y1='{T}' x2='{L}' y2='{T+plot_h}' "
                 f"stroke='#333'/>")
    parts.append(f"<line x1='{L}' y1='{T+plot_h}' x2='{W-R}' y2='{T+plot_h}' "
                 f"stroke='#333'/>")

    for i, r in enumerate(sim):
        cx = L + slot * (i + 0.5)
        ex, ac = r["expected"], r["actual"]
        ok = r["match"]
        # expected bar (blue), actual bar (green if match else red)
        x1 = cx - bw - 2
        x2 = cx + 2
        parts.append(f"<rect x='{x1:.1f}' y='{y(ex):.1f}' width='{bw:.1f}' "
                     f"height='{T+plot_h-y(ex):.1f}' fill='#4477cc'/>")
        col = "#2e9e5b" if ok else "#d23c3c"
        parts.append(f"<rect x='{x2:.1f}' y='{y(ac):.1f}' width='{bw:.1f}' "
                     f"height='{T+plot_h-y(ac):.1f}' fill='{col}'/>")
        # value labels
        parts.append(f"<text x='{x1+bw/2:.1f}' y='{y(ex)-4:.1f}' "
                     f"text-anchor='middle' font-size='10' fill='#4477cc'>{ex}</text>")
        parts.append(f"<text x='{x2+bw/2:.1f}' y='{y(ac)-4:.1f}' "
                     f"text-anchor='middle' font-size='10' fill='{col}'>{ac}</text>")
        # x label (name + k), angled
        label = f"{r['name']} k={r['k']}"
        ty = T + plot_h + 14
        parts.append(f"<text x='{cx:.1f}' y='{ty:.1f}' text-anchor='end' "
                     f"font-size='10' fill='#333' transform='rotate(-35 {cx:.1f} {ty:.1f})'>"
                     f"{label}</text>")

    # legend
    lx, ly = L + 10, T + 6
    parts.append(f"<rect x='{lx}' y='{ly}' width='12' height='12' fill='#4477cc'/>")
    parts.append(f"<text x='{lx+18}' y='{ly+11}' font-size='12'>expected α(G′)</text>")
    parts.append(f"<rect x='{lx}' y='{ly+18}' width='12' height='12' fill='#2e9e5b'/>")
    parts.append(f"<text x='{lx+18}' y='{ly+29}' font-size='12'>actual (sim) — green=match, red=mismatch</text>")
    parts.append("</svg>")
    return "\n".join(parts)


# ── SVG scatter: actual vs expected with the y=x agreement line ──────────────

def _scatter_svg(rows: List[dict]) -> str:
    sim = [r for r in rows if r.get("simulated")]
    if not sim:
        return "<svg xmlns='http://www.w3.org/2000/svg'/>"
    W = H = 420
    M = 50
    span = W - 2 * M
    vmax = max(max(r["expected"], r["actual"]) for r in sim)
    vmax = max(vmax, 1)

    def px(v): return M + (v / vmax) * span
    def py(v): return H - M - (v / vmax) * span

    parts = [
        f"<svg xmlns='http://www.w3.org/2000/svg' width='{W}' height='{H}' "
        f"viewBox='0 0 {W} {H}' font-family='sans-serif'>",
        "<rect width='100%' height='100%' fill='white'/>",
        f"<text x='{W/2}' y='24' text-anchor='middle' font-size='15' "
        f"font-weight='bold'>actual vs expected (on the line = exact)</text>",
        # y=x reference
        f"<line x1='{px(0):.1f}' y1='{py(0):.1f}' x2='{px(vmax):.1f}' "
        f"y2='{py(vmax):.1f}' stroke='#bbb' stroke-dasharray='4,4'/>",
        f"<line x1='{M}' y1='{H-M}' x2='{W-M}' y2='{H-M}' stroke='#333'/>",
        f"<line x1='{M}' y1='{M}' x2='{M}' y2='{H-M}' stroke='#333'/>",
        f"<text x='{W/2}' y='{H-12}' text-anchor='middle' font-size='12'>expected α(G′)</text>",
        f"<text x='16' y='{H/2}' text-anchor='middle' font-size='12' "
        f"transform='rotate(-90 16 {H/2})'>actual (sim)</text>",
    ]
    for v in range(0, vmax + 1):
        parts.append(f"<text x='{px(v):.1f}' y='{H-M+16:.1f}' text-anchor='middle' "
                     f"font-size='10' fill='#555'>{v}</text>")
        parts.append(f"<text x='{M-8}' y='{py(v)+4:.1f}' text-anchor='end' "
                     f"font-size='10' fill='#555'>{v}</text>")
    # jitter overlapping points slightly for visibility
    from collections import defaultdict
    seen = defaultdict(int)
    for r in sim:
        key = (r["expected"], r["actual"])
        j = seen[key]; seen[key] += 1
        off = (j % 4) * 3.0
        col = "#2e9e5b" if r["match"] else "#d23c3c"
        parts.append(f"<circle cx='{px(r['expected'])+off:.1f}' "
                     f"cy='{py(r['actual'])-off:.1f}' r='5' fill='{col}' "
                     f"fill-opacity='0.75'/>")
    parts.append("</svg>")
    return "\n".join(parts)


def _terminal_chart(rows: List[dict]) -> None:
    sim = [r for r in rows if r.get("simulated")]
    if not sim:
        return
    try:
        import plotext as plt
    except Exception:
        return
    labels = [f"{r['name'].split()[0]}·k{r['k']}" for r in sim]
    plt.clf()
    plt.simple_multiple_bar(
        labels, [[r["expected"] for r in sim], [r["actual"] for r in sim]],
        labels=["expected", "actual"],
        title="expected α(G') vs actual Rydberg-MWIS")
    plt.show()


def _decomp_svg(rows: List[dict]) -> str:
    """Whole-graph n·k (would be skipped) vs max piece slots actually simulated,
    with the monolithic-wall line at 16."""
    if not rows:
        return "<svg xmlns='http://www.w3.org/2000/svg'/>"
    W, H = 1000, 460
    L, R, T, B = 60, 20, 60, 90
    plot_w, plot_h = W - L - R, H - T - B
    ymax = max(max(r["whole_slots"], r["max_piece_slots"]) for r in rows)
    ymax = max(ymax, 16) + 4
    ng = len(rows)
    slot = plot_w / ng
    bw = slot * 0.30

    def y(v): return T + plot_h - (v / ymax) * plot_h

    parts = [
        f"<svg xmlns='http://www.w3.org/2000/svg' width='{W}' height='{H}' "
        f"viewBox='0 0 {W} {H}' font-family='sans-serif'>",
        "<rect width='100%' height='100%' fill='white'/>",
        f"<text x='{W/2}' y='26' text-anchor='middle' font-size='17' "
        f"font-weight='bold'>Decomposition: whole n·k vs max simulated piece "
        f"(device size stays small)</text>",
    ]
    for v in range(0, ymax + 1, 10):
        yy = y(v)
        parts.append(f"<line x1='{L}' y1='{yy:.1f}' x2='{W-R}' y2='{yy:.1f}' "
                     f"stroke='#eee'/>")
        parts.append(f"<text x='{L-8}' y='{yy+4:.1f}' text-anchor='end' "
                     f"font-size='11' fill='#555'>{v}</text>")
    # the monolithic wall at 16
    yw = y(16)
    parts.append(f"<line x1='{L}' y1='{yw:.1f}' x2='{W-R}' y2='{yw:.1f}' "
                 f"stroke='#d23c3c' stroke-dasharray='6,4' stroke-width='1.5'/>")
    parts.append(f"<text x='{W-R-4}' y='{yw-5:.1f}' text-anchor='end' "
                 f"font-size='12' fill='#d23c3c'>monolithic wall NK_MAX = 16</text>")
    parts.append(f"<line x1='{L}' y1='{T}' x2='{L}' y2='{T+plot_h}' stroke='#333'/>")
    parts.append(f"<line x1='{L}' y1='{T+plot_h}' x2='{W-R}' y2='{T+plot_h}' stroke='#333'/>")

    for i, r in enumerate(rows):
        cx = L + slot * (i + 0.5)
        whole, piece = r["whole_slots"], r["max_piece_slots"]
        x1, x2 = cx - bw - 2, cx + 2
        parts.append(f"<rect x='{x1:.1f}' y='{y(whole):.1f}' width='{bw:.1f}' "
                     f"height='{T+plot_h-y(whole):.1f}' fill='#cc7a44'/>")
        parts.append(f"<rect x='{x2:.1f}' y='{y(piece):.1f}' width='{bw:.1f}' "
                     f"height='{T+plot_h-y(piece):.1f}' fill='#2e9e5b'/>")
        parts.append(f"<text x='{x1+bw/2:.1f}' y='{y(whole)-4:.1f}' "
                     f"text-anchor='middle' font-size='10' fill='#cc7a44'>{whole}</text>")
        parts.append(f"<text x='{x2+bw/2:.1f}' y='{y(piece)-4:.1f}' "
                     f"text-anchor='middle' font-size='10' fill='#2e9e5b'>{piece}</text>")
        ty = T + plot_h + 14
        parts.append(f"<text x='{cx:.1f}' y='{ty:.1f}' text-anchor='end' "
                     f"font-size='10' fill='#333' transform='rotate(-30 {cx:.1f} {ty:.1f})'>"
                     f"{r['name']} k={r['k']}</text>")
    lx, ly = L + 10, T + 6
    parts.append(f"<rect x='{lx}' y='{ly}' width='12' height='12' fill='#cc7a44'/>")
    parts.append(f"<text x='{lx+18}' y='{ly+11}' font-size='12'>whole-graph n·k (monolithic — would skip)</text>")
    parts.append(f"<rect x='{lx}' y='{ly+18}' width='12' height='12' fill='#2e9e5b'/>")
    parts.append(f"<text x='{lx+18}' y='{ly+29}' font-size='12'>max piece slots actually simulated</text>")
    parts.append("</svg>")
    return "\n".join(parts)


def make_decomp(rows: List[dict], outdir: str, fname: str = "decomp.svg") -> None:
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, fname), "w") as fh:
        fh.write(_decomp_svg(rows))
    print(f"wrote {outdir}/{fname}")
    try:
        import plotext as plt
        sim = rows
        labels = [r["name"].split()[0][:8] for r in sim]
        plt.clf()
        plt.simple_multiple_bar(
            labels, [[r["whole_slots"] for r in sim],
                     [r["max_piece_slots"] for r in sim]],
            labels=["whole n·k", "max piece"],
            title="whole-graph n·k vs max simulated piece (decomposition)")
        plt.show()
    except Exception:
        pass


def make_all(rows: List[dict], outdir: str) -> None:
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "bars.svg"), "w") as fh:
        fh.write(_bar_chart_svg(rows))
    with open(os.path.join(outdir, "scatter.svg"), "w") as fh:
        fh.write(_scatter_svg(rows))
    print(f"wrote {outdir}/bars.svg and scatter.svg")
    print()
    _terminal_chart(rows)


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results", "results.json")) as fh:
        rows = json.load(fh)
    make_all(rows, os.path.join(here, "results"))
