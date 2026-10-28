# Antal–Pisztora projected box estimate

The proposition `LatticeProb.External.AntalPisztoraProjectedBox` is an
**unproved cited input**. It records a finite-box consequence of Peter Antal
and Agoston Pisztora, “On the chemical distance for supercritical Bernoulli
percolation,” *The Annals of Probability* 24(2), 1036–1048 (1996), equations
(2.7), (2.9), and (2.24). The referenced PDF has SHA-256
`ff0b2b4bda6cd34dfb132c478138a0fe56a6a566f503f4776dda54ab0fe4d411`.

For each dimension d ≥ 2 and Bernoulli bond parameter pc(d) < p < 1,
the proposition asserts the existence of positive constants C and c and a
natural number N₀, all chosen before the scale and center. For every positive
integer N with N₀ ≤ N, N > 10 and 8 dividing N, and every integer center a,
the complement of the projected event has probability at most C exp(−cN).
The law is the independent nearest-neighbor Bernoulli bond law.

The outer box is the integer intersection of the closed cube of radius 5N/4
centered at a. The event requires one unique outer crossing component. Every
open walk in that box whose trace has a coordinate gap greater than N/2 is
attached to that component. For every contained integer-corner cube of side
exactly N and each coordinate direction, an open path inside that inner cube
joins its opposite faces and lies in the same **global outer component**;
the paths for different directions need not share an inner component.

The cited event implies this projection: the retained inner cubes form a
subfamily of the original subboxes, and their side N is strictly larger than
N/10. For the attachment clause, interpret the source's path radius as a
standard anchored, enclosing, or intrinsic radius: it is at least half the
ambient ℓ∞ trace diameter, so a gap greater than N/2 triggers the original
radius threshold. This is an explicit interpretation of the source wording.
The bound at arbitrary integer centers follows by stationarity of the iid
bond law. This proposition does not establish the bound, a multiscale box
result, or any paper theorem.
