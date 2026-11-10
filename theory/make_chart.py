#!/usr/bin/env python3
"""Standalone SVG/HTML of computed schedule bounds, using only stdlib."""
import json, math
rows=json.load(open('theory/large_uniform_results.json'))
W,H=700,310
left,right,top,bottom=80,20,20,55
cw,ch=W-left-right,H-top-bottom
x=lambda v:left+(math.log10(v)-4)/5*cw
y=lambda v:top+(6-math.log10(v))/5*ch
svg=[f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img" aria-label="Constructed schedules: quantum space and oracle step overhead, logarithmic axes">',
'<style>text{fill:var(--foreground,#222);font:12px sans-serif}.grid{stroke:var(--border,#ddd);stroke-width:1}.series{fill:none;stroke-width:2}circle{stroke-width:1}</style>']
for power in range(4,10):
    xp=x(10**power);svg.append(f'<line class="grid" x1="{xp}" y1="{top}" x2="{xp}" y2="{top+ch}"/><text x="{xp}" y="{top+ch+19}" text-anchor="middle">10^{power}</text>')
for power in range(1,7):
    yp=y(10**power);svg.append(f'<line class="grid" x1="{left}" y1="{yp}" x2="{left+cw}" y2="{yp}"/><text x="{left-10}" y="{yp+4}" text-anchor="end">10^{power}</text>')
colors=['var(--chart-1,#4169e1)','var(--chart-2,#cf6435)','var(--chart-3,#258548)']
for index,m in enumerate((1000,100000,10000000)):
    points=[row for row in rows if row['m']==m]
    coordinates=' '.join(f"{x(row['space'])},{y(row['oracle_step_factor'])}" for row in points)
    color=colors[index]
    svg.append(f'<polyline class="series" stroke="{color}" points="{coordinates}"/>')
    for row in points:
        xp,yp=x(row['space']),y(row['oracle_step_factor'])
        svg.append(f'<circle cx="{xp}" cy="{yp}" r="4" fill="{color}"><title>m={m}; r={row["r"]}; S={row["space"]}; 2C/T={row["oracle_step_factor"]:.4f}</title></circle>')
    svg.append(f'<text x="{left+15+index*185}" y="{H-5}" style="fill:{color}">m = 10^{int(math.log10(m))} bits</text>')
svg.append(f'<text x="{left+cw/2}" y="{H-26}" text-anchor="middle">Peak space bound S (qubits)</text>')
svg.append(f'<text transform="translate(18,{top+ch/2}) rotate(-90)" text-anchor="middle">Oracle step cost / T</text></svg>')
svg=''.join(svg)
open('theory/balanced_tradeoff.svg','w').write(svg)
html='<!doctype html><html><head><meta charset="utf-8"><style>:root{color-scheme:light dark}body{margin:0;font-family:var(--font-sans,sans-serif);color:var(--foreground)}svg{display:block;width:100%;height:auto}p{font-size:13px;line-height:1.45;margin:8px 0}</style></head><body><p><strong>Balanced schedules at T = 10⁹</strong> · a = 1, k = 0. Each curve fixes m; its points use r = 1, 10, 1000 bits.</p>'+svg+'<p>Each point minimises the space bound among balanced depths. These are constructed schedule costs, not unrestricted optima. Logarithmic axes; interface and evaluator workspace excluded.</p></body></html>'
open('theory/balanced_tradeoff.html','w').write(html)
