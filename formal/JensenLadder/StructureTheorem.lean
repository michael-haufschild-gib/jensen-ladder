import Mathlib.Tactic

/-!
# Structure Theorem consumer algebra

This module formalizes the deterministic bookkeeping behind the conditional
Structure Theorem: once bulk, edge, top, boundary, and residual certificate rows
are supplied, every nondegenerate bad packet is confined to the Lehmer-window
residue.

The predicates below are deliberately abstract.  They do not construct the
actual xi bulk phase representation, Airy/Langer cells, residual-to-Lehmer map,
finite base, or arithmetic Row A1.  Those are the open analytic rows described
in `docs/rh/structure_theorem_t1_t2_lehmer_windows.md` and
`docs/rh/analytic_gap_closure_20260613.md`.

## Honest scope

This proves only regional gluing and certificate consumption.  It is not a proof
of `CV(d)`, global xi-Jensen hyperbolicity, or the Riemann Hypothesis.  Theorem M
is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace StructureTheorem

/-- Labels for the regional decomposition used by the Structure Theorem
consumer. -/
inductive Region where
  | bulk
  | edge
  | top
  | residual
  deriving DecidableEq

/-- A5a, in predicate form: if `Residual` is defined as the complement of the
bulk/edge/top regions inside the positive axis, then every positive point is in
one of the four regions. -/
theorem residual_cover_by_definition
    {Point : Type*}
    {Positive Bulk Edge Top Residual : Point → Prop}
    (hResidual_def :
      ∀ x, Residual x ↔ Positive x ∧ ¬ Bulk x ∧ ¬ Edge x ∧ ¬ Top x) :
    ∀ x, Positive x → Bulk x ∨ Edge x ∨ Top x ∨ Residual x := by
  intro x hpos
  by_cases hBulk : Bulk x
  · exact Or.inl hBulk
  by_cases hEdge : Edge x
  · exact Or.inr (Or.inl hEdge)
  by_cases hTop : Top x
  · exact Or.inr (Or.inr (Or.inl hTop))
  exact Or.inr (Or.inr (Or.inr ((hResidual_def x).2 ⟨hpos, hBulk, hEdge, hTop⟩)))

/-- A5c, membership half: if every residual bad packet is covered by one of the
certified Lehmer cells, and `Lehmer` is the union of those cells, then every
residual bad packet lies in `Lehmer`. -/
theorem residual_bad_mem_lehmer_of_cover
    {Point CellIndex : Type*}
    {Residual Bad Lehmer : Point → Prop}
    {Cell : CellIndex → Point → Prop}
    (hLehmer_def : ∀ x, Lehmer x ↔ ∃ j : CellIndex, Cell j x)
    (hCover : ∀ x, Residual x → Bad x → ∃ j : CellIndex, Cell j x) :
    ∀ x, Residual x → Bad x → Lehmer x := by
  intro x hResidual hBad
  exact (hLehmer_def x).2 (hCover x hResidual hBad)

/-- A5c, certificate half: a residual bad packet covered by a certified cell
inherits the packet-validity row and the Lehmer-scale gap row attached to that
cell.  `LehmerScale j` abstracts the quantitative row
`gap_{d,j} <= tau_L / log(T_{d,j})`. -/
theorem residual_bad_lehmer_scale_certificate
    {Point CellIndex : Type*}
    {Residual Bad : Point → Prop}
    {Cell : CellIndex → Point → Prop}
    {PacketValid LehmerScale : CellIndex → Prop}
    (hCover : ∀ x, Residual x → Bad x → ∃ j : CellIndex, Cell j x)
    (hPacket : ∀ j x, Cell j x → PacketValid j)
    (hScale : ∀ j, PacketValid j → LehmerScale j) :
    ∀ x, Residual x → Bad x →
      ∃ j : CellIndex, Cell j x ∧ PacketValid j ∧ LehmerScale j := by
  intro x hResidual hBad
  rcases hCover x hResidual hBad with ⟨j, hCell⟩
  have hValid : PacketValid j := hPacket j x hCell
  exact ⟨j, hCell, hValid, hScale j hValid⟩

/-- ST-large regional confinement: if the four-region cover holds, bulk/edge/top
regions exclude bad packets, and residual bad packets are placed in `Lehmer`,
then every positive bad packet is Lehmer-confined. -/
theorem large_degree_confinement
    {Degree Point : Type*}
    {Large : Degree → Prop}
    {Positive Bad Bulk Edge Top Residual Lehmer : Degree → Point → Prop}
    (hCover : ∀ d x, Large d → Positive d x →
      Bulk d x ∨ Edge d x ∨ Top d x ∨ Residual d x)
    (hBulkSafe : ∀ d x, Large d → Bad d x → Bulk d x → False)
    (hEdgeSafe : ∀ d x, Large d → Bad d x → Edge d x → False)
    (hTopSafe : ∀ d x, Large d → Bad d x → Top d x → False)
    (hResidualLehmer : ∀ d x, Large d → Bad d x → Residual d x → Lehmer d x) :
    ∀ d x, Large d → Positive d x → Bad d x → Lehmer d x := by
  intro d x hLarge hPositive hBad
  rcases hCover d x hLarge hPositive with hBulk | hEdge | hTop | hResidual
  · exact False.elim (hBulkSafe d x hLarge hBad hBulk)
  · exact False.elim (hEdgeSafe d x hLarge hBad hEdge)
  · exact False.elim (hTopSafe d x hLarge hBad hTop)
  · exact hResidualLehmer d x hLarge hBad hResidual

/-- A5d regional handoff consumer.  A cell/boundary decomposition plus interior
and boundary safety rows confines every positive bad packet to the residual
Lehmer certificate. -/
theorem regional_handoff_confinement
    {Point CellIndex : Type*}
    {Positive Bad Boundary Residual Lehmer : Point → Prop}
    {Cell : CellIndex → Point → Prop}
    {label : CellIndex → Region}
    (hDecomp : ∀ x, Positive x → (∃ c : CellIndex, Cell c x) ∨ Boundary x)
    (hBulkSafe : ∀ c x, label c = Region.bulk → Cell c x → Bad x → False)
    (hEdgeSafe : ∀ c x, label c = Region.edge → Cell c x → Bad x → False)
    (hTopSafe : ∀ c x, label c = Region.top → Cell c x → Bad x → False)
    (hResidualCell : ∀ c x, label c = Region.residual → Cell c x → Bad x → Residual x)
    (hBoundary : ∀ x, Boundary x → Bad x → Residual x)
    (hResidualLehmer : ∀ x, Residual x → Bad x → Lehmer x) :
    ∀ x, Positive x → Bad x → Lehmer x := by
  intro x hPositive hBad
  rcases hDecomp x hPositive with ⟨c, hCell⟩ | hBoundaryX
  · cases hLabel : label c with
    | bulk =>
        exact False.elim (hBulkSafe c x hLabel hCell hBad)
    | edge =>
        exact False.elim (hEdgeSafe c x hLabel hCell hBad)
    | top =>
        exact False.elim (hTopSafe c x hLabel hCell hBad)
    | residual =>
        exact hResidualLehmer x (hResidualCell c x hLabel hCell hBad) hBad
  · exact hResidualLehmer x (hBoundary x hBoundaryX hBad) hBad

end StructureTheorem
end JensenLadder
