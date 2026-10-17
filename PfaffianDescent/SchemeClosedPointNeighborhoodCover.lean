import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Separation.Basic

/-! Actual neighborhoods of every closed point cover a compact scheme.
A nonempty closed complement contains an actual closed point by compactness
and the scheme's genuine T0 structure; no cover/classification certificate.
SOURCE ONLY / UNVERIFIED. -/
namespace PfaffianDescent
open AlgebraicGeometry TopologicalSpace
universe u

/-- An actual neighborhood at EVERY closed point covers the SAME compact
scheme. This uses genuine compact T0 topology, not Jacobsonity or a
classification of all scheme points. Empty schemes are included. -/
theorem schemeClosedPointNeighborhoods_cover_top
    (X : Scheme.{u}) [CompactSpace X]
    (U : closedPoints X → X.Opens) (hU : ∀ P, P.1 ∈ U P) :
    (⊤ : X.Opens) ≤ ⨆ P, U P := by
  intro x _hx
  by_contra hx
  have hclosed : IsClosed ((⨆ P, U P : X.Opens) : Set X)ᶜ :=
    (⨆ P, U P : X.Opens).isOpen.isClosed_compl
  obtain ⟨y, hy, hyclosed⟩ := hclosed.exists_closed_singleton ⟨x, hx⟩
  exact hy ((Opens.mem_iSup).mpr ⟨⟨y, hyclosed⟩, hU ⟨y, hyclosed⟩⟩)

end PfaffianDescent
