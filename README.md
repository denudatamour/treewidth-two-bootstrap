# From theta graphs to quadratic time in graph bootstrap percolation

Haimin Zhou · Independent Researcher

**[Read the full preprint (PDF)](https://github.com/denudatamour/treewidth-two-bootstrap/releases/download/preprint-v1.0/treewidth-two-bootstrap-v1.0.pdf)** · [Preprint v1.0, 2026-11-20](https://github.com/denudatamour/treewidth-two-bootstrap/releases/tag/preprint-v1.0)

Fix a finite simple graph $H$. Start with any graph on $n$ vertices. In one round, add every missing edge that completes a copy of $H$ using edges already present at the start of the round. Write $M_H(n)$ for the greatest possible number of rounds until no further edge can be added. The rule $H$ stays fixed as $n$ grows.

Fabian, Morris and Szabó asked whether every rule of treewidth two satisfies $M_H(n)=O_H(n)$. The first two results below explain why a linear bound holds for theta graphs and for an entire class containing them. The third gives a fixed rule of treewidth two for which the maximum running time is quadratic. [Original conjecture, §8.3, Conjecture 8.8](https://arxiv.org/html/2311.18786v2#S8.SS3) · [Survey, Conjecture 7.14](https://arxiv.org/html/2602.12736v2#S7.SS5)

## I. Theta graphs

Join two vertices by three internally disjoint paths of fixed lengths $a,b,c\ge 2$. For the resulting theta rule, $M_H(n)=\Theta_H(n)$. Starting the rule on $H$ itself can give three different outcomes. Mixed path parities give a clique, lengths of one parity that are not all equal give a complete bipartite graph, and three equal lengths leave $H$ stable. All three cases still have linear worst-case time over arbitrary starting graphs. [Theta preprint, version 1.0](https://doi.org/10.5281/zenodo.24227363)

## II. A structural reason for linear time

Let $H$ be connected. If every edge has an endpoint of degree **exactly two** in $H$, then $M_H(n)=O_H(n)$. If also $\delta(H)\ge 2$ and $\Delta(H)\ge 3$, the order is $\Theta_H(n)$. This includes any fixed number $k\ge 3$ of internally disjoint paths of lengths at least two joining the same two vertices. The upper bound uses the degree-two vertices to propagate adjacency. The matching lower bound in the stated range follows from Fabian, Morris and Szabó. [Proof outline](PROOF-OUTLINE.md#ii-how-degree-two-vertices-control-the-clock) · [Theorem 1.4](https://arxiv.org/html/2311.18786v2#S1.SS4)

## III. A quadratic rule of treewidth two

There is a fixed 2-connected rule $H$ with treewidth two, minimum degree two and 166,464 vertices for which $M_H(n)=\Theta(n^2)$. Two cyclic indices of lengths $p$ and $q$ advance together by one step in each direction per round. With coprime lengths of comparable size, their joint period is quadratic in $p+q$. The construction enforces this motion using ordinary, uncoloured copies of $H$. Treewidth two is a condition on the rule. The connected starting graphs in the construction have order $69{,}360(p+q)$ and uniformly bounded initial maximum degree. [Construction and proof outline](PROOF-OUTLINE.md#iii-why-an-ordinary-graph-can-take-quadratic-time)

The theta theorem is available as a public preprint. The degree-two theorem and the quadratic construction have undergone independent AI-assisted mathematical checks. Human peer review is pending.

Contact Haimin Zhou at haiminzhou.1@gmail.com. This research was conducted with AI assistance. [Citation](CITATION.cff) · [CC BY 4.0](LICENSE)
