import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual open chart above the actual finite parameter open has a
quasi-finite actual closed zero map. -/
theorem cubicClosedPointSerreFiniteZeroResidual_comap_zero_locallyQuasiFinite_of_range_goodOpen
    {A B T E : Scheme.{u}} (I : A.IdealSheafData) (π : A ⟶ B)
    [IsProper (I.subschemeι ≫ π)]
    (v : T ⟶ A) [IsOpenImmersion v] (r : E ⟶ B) [IsOpenImmersion r]
    (f : T ⟶ E) (hf : v ≫ π = f ≫ r)
    (hr : Set.range r ⊆ cubicClosedPointSerreFiniteZeroResidual_goodOpen (I.subschemeι ≫ π)) :
    LocallyQuasiFinite ((I.comap v).subschemeι ≫ f) := by
  let w : (I.comap v).subscheme ⟶ I.subscheme :=
    (I.comapIso v).hom ≫ pullback.snd v I.subschemeι
  letI : IsOpenImmersion w := by dsimp [w]; infer_instance
  have hw : w ≫ I.subschemeι = (I.comap v).subschemeι ≫ v := by
    simp only [w, Category.assoc, ← pullback.condition, I.comapIso_hom_fst_assoc]
  have hc : w ≫ (I.subschemeι ≫ π) = ((I.comap v).subschemeι ≫ f) ≫ r := by
    rw [← Category.assoc, hw, Category.assoc, hf, ← Category.assoc]
  letI : LocallyOfFiniteType (((I.comap v).subschemeι ≫ f) ≫ r) := by
    rw [← hc]
    infer_instance
  letI : LocallyOfFiniteType ((I.comap v).subschemeι ≫ f) :=
    locallyOfFiniteType_of_comp _ r
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  ext z
  have hy : (I.subschemeι ≫ π) (w z) ∈
      cubicClosedPointSerreFiniteZeroResidual_goodOpen (I.subschemeι ≫ π) := by
    have hp := congrArg (fun q : (I.comap v).subscheme ⟶ B => q z) hc
    change (I.subschemeι ≫ π) (w z) = r (((I.comap v).subschemeι ≫ f) z) at hp
    rw [hp]
    exact hr ⟨_, rfl⟩
  have hq : (w ≫ (I.subschemeι ≫ π)).QuasiFiniteAt z :=
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr (hy _ rfl)
  rw [hc, Scheme.Hom.quasiFiniteAt_comp_iff] at hq
  simpa using hq

end PfaffianDescent
