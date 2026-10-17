import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleStalkOpen
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_closed_field_stalk_open
    {T Z : Scheme.{u}} (i : T ⟶ Z) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i]
    (hf : ∀ x : T, IsField (Z.presheaf.stalk (i x))) : IsOpenImmersion i := by
  have hm : ∀ x : T, x ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen i := by
    intro x
    letI : Field (Z.presheaf.stalk (i x)) := (hf x).toField
    have hb : Function.Bijective (i.stalkMap x).hom :=
      ⟨(i.stalkMap x).hom.injective, i.stalkMap_surjective x⟩
    apply cubicClosedPointSerreFiniteZeroResidual_mem_etaleOpen_of_formallyEtale_stalk i x
    exact (cubicClosedPointSerreFiniteZeroResidual_formallyEtale_iff _).mpr
      ⟨RingHom.FormallyUnramified.of_surjective hb.2, RingHom.FormallySmooth.of_bijective hb⟩
  have hW : cubicClosedPointSerreFiniteZeroResidual_etaleOpen i = ⊤ := by
    apply top_unique
    intro x hx
    exact hm x
  have ht := cubicClosedPointSerreFiniteZeroResidual_etaleOpen_etale i
  rw [hW] at ht
  letI : Etale ((⊤ : T.Opens).ι ≫ i) := ht
  let a := T.topIso
  have he : i = a.inv ≫ ((⊤ : T.Opens).ι ≫ i) := by
    change i = T.topIso.inv ≫ (T.topIso.hom ≫ i)
    simp only [Iso.inv_hom_id_assoc]
  letI : Etale i := by rw [he]; infer_instance
  exact IsOpenImmersion.of_flat_of_mono i

end PfaffianDescent
