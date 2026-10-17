import PfaffianDescent.GrassmannianGraph
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Logic.Equiv.Fintype

namespace PfaffianDescent
open Module
section
variable {R M ι : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] (bM : Basis ι R M) {n : ℕ}

/-- Over a local ring, a locally free quotient has a basis selected from the ambient coordinate basis. -/
theorem grassmannian_local_quotient_basis (W : Module.Grassmannian R M n) :
    ∃ (a : Fin n ↪ ι) (b : Basis (Fin n) R (M ⧸ W.toSubmodule)),
      ∀ i, b i = W.toSubmodule.mkQ (bM (a i)) := by
  classical
  let q := W.toSubmodule.mkQ
  haveI : Module.FinitePresentation R (M ⧸ W.toSubmodule) := Module.finitePresentation_of_projective R _
  have hq : Submodule.span R (Set.range (q ∘ bM)) = ⊤ := by
    rw [Set.range_comp, Submodule.span_image, bM.span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat (q ∘ bM) hq
  letI : Module.Free R (M ⧸ W.toSubmodule) := Module.Free.of_basis b
  haveI : Finite κ := Module.Finite.finite_basis b
  letI : Fintype κ := Fintype.ofFinite κ
  have hn : Module.finrank R (M ⧸ W.toSubmodule) = n := by
    exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := R) (M := M ⧸ W.toSubmodule)) (IsLocalRing.closedPoint R)).symm.trans
        (W.rankAtStalk_eq (IsLocalRing.closedPoint R))
  have hk : Fintype.card κ = n := (Module.finrank_eq_card_basis b).symm.trans hn
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hk
  have ha : Function.Injective a := by
    intro i j hij
    apply b.injective
    rw [hb, hb, hij]
  let a' : Fin n ↪ ι := ⟨a ∘ e.symm, ha.comp e.symm.injective⟩
  refine ⟨a', b.reindex e, ?_⟩
  intro i
  rw [Basis.reindex_apply]
  exact hb (e.symm i)

end
end PfaffianDescent
