# Mathematical statement and proof correspondence

## Original problem and exact scope

Erdős Problem 602 asks about a possibly uncountable family of countably infinite sets with finite
pairwise intersections of size different from one. The question is whether a two-coloring can
avoid every monochromatic member. The catalog identifies it as JSP-000489.

The reference Lean file has an unproved `erdos_602.variants.countable_index` statement and explicitly
notes that Bernstein's lemma makes all intersection conditions unnecessary when the index is
countable. We prove that entire scoped case, and the classical stronger simultaneous splitting:

For every `A : Nat -> Set alpha`, assuming `A i` is infinite for every `i`, there is
`f : alpha -> Nat` such that `{x | x belongs to A i and f x = c}` is infinite for every `i,c`.

The ground universe is arbitrary. Individual sets need not be countable. `Set.Infinite` is
literal infinitude, not a large-cardinality cutoff. The final Property B theorem has exactly the
usual absence of a constant color on each set. Its coloring is defined on all of the ground set,
which is stronger than defining it only on the union; restricting it to the union gives the
original coloring domain.

## Construction

Enumerate all triples `(i,c,r)` of natural numbers with the standard pairing function. At each
stage choose a fresh point in the requested set, avoiding the finite set of all previously chosen
points. Infinitude proves that such a point exists. The selected sequence is injective.
Give the point selected for `(i,c,r)` color `c` and extend the coloring elsewhere. For any fixed
`i,c`, varying `r` gives an injective sequence in that set and color class, proving infinitude.
Reduce the natural-number colors modulo any positive `q` to get `q` colors. With `q=2`, every
set contains both colors and cannot be monochromatic.

`Classical.choose` is applied only to proved existence results. The inverse-function construction
is justified by the proved injectivity; it is not an assumption or an external mathematical oracle.

## Theorem map

| Theorem | Role |
|---|---|
| `fresh_spec` | A selected point belongs to the requested infinite set and is unused. |
| `history_mono` | Previously selected points remain in the finite history. |
| `picked_mem` | Every point satisfies its requested membership condition. |
| `picked_ne_of_lt` | Later stages never reuse earlier points. |
| `picked_injective` | All selected points are pairwise distinct. |
| `infinitely_many_each_color` | Simultaneous natural-color splitting of every set. |
| `finite_color_splitting` | Every positive finite palette occurs infinitely in every set. |
| `bernstein_propertyB` | Complete countable-index two-color theorem. |

Negative controls replace the coloring by a constant and force the selection to reuse its first
point. They must fail, alongside false arithmetic and unapproved-assumption controls. Finite Python
examples are additional checks, not substitutes for the infinite Lean proof.
