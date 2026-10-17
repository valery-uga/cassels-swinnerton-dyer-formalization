import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Cover.Open

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace PfaffianDescent

/-- Whole ideals on an actual affine-chart open cover determine the entire
original ideal sheaf. The native chart maps need not be chosen open inclusions. -/
theorem wholeIdeal_eq_of_affineOpenCover_comaps
    {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) [∀ (i : 𝒰.I₀), IsAffine (𝒰.X i)]
    {J J' : X.IdealSheafData}
    (h : ∀ (i : 𝒰.I₀), J.comap (𝒰.f i) = J'.comap (𝒰.f i)) : J = J' := by
  let A (i : 𝒰.I₀) : X.affineOpens :=
    ⟨𝒰.f i ''ᵁ (⊤ : (𝒰.X i).Opens),
      (isAffineOpen_top (𝒰.X i)).image_of_isOpenImmersion (𝒰.f i)⟩
  have hA : ⨆ i, (A i).1 = ⊤ := by
    simpa only [A, Scheme.Hom.image_top_eq_opensRange] using 𝒰.iSup_opensRange
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top A hA
  intro i
  let V : (𝒰.X i).affineOpens := ⟨⊤, isAffineOpen_top (𝒰.X i)⟩
  have he := congrArg (fun L : (𝒰.X i).IdealSheafData => L.ideal V) (h i)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J (𝒰.f i) V,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J' (𝒰.f i) V] at he
  change (J.ideal (A i)).comap ((𝒰.f i).appIso V).inv.hom =
    (J'.ideal (A i)).comap ((𝒰.f i).appIso V).inv.hom at he
  exact Ideal.comap_injective_of_surjective ((𝒰.f i).appIso V).inv.hom
    (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso V).inv).surjective he

/-- On an arbitrary actual open cover, equality of the whole native comaps
forces equality of the whole global ideals; no gluing certificate is assumed. -/
theorem wholeIdeal_eq_of_openCover_comaps
    {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) {J J' : X.IdealSheafData}
    (h : ∀ (i : 𝒰.I₀), J.comap (𝒰.f i) = J'.comap (𝒰.f i)) : J = J' := by
  let 𝒱 := 𝒰.affineRefinement.openCover
  let r : 𝒱 ⟶ 𝒰 := 𝒰.fromAffineRefinement
  letI (i : 𝒱.I₀) : IsAffine (𝒱.X i) := by
    change IsAffine (Spec (𝒰.affineRefinement.X i))
    infer_instance
  apply wholeIdeal_eq_of_affineOpenCover_comaps 𝒱
  intro i
  calc
    J.comap (𝒱.f i) = (J.comap (𝒰.f (r.s₀ i))).comap (r.h₀ i) := by
      rw [← r.w₀ i, Scheme.IdealSheafData.comap_comp]
    _ = (J'.comap (𝒰.f (r.s₀ i))).comap (r.h₀ i) :=
      congrArg (fun L : (𝒰.X (r.s₀ i)).IdealSheafData => L.comap (r.h₀ i)) (h (r.s₀ i))
    _ = J'.comap (𝒱.f i) := by
      rw [← Scheme.IdealSheafData.comap_comp, r.w₀ i]

/-- Whole local comparisons on the actual pulled-back open cover determine
exactly the native pullback of the original global ideal. -/
theorem wholeIdeal_pullback_eq_of_openCover_comaps
    {X Y : Scheme.{u}} (f : Y ⟶ X) (𝒰 : X.OpenCover.{u})
    (J : X.IdealSheafData) (K : Y.IdealSheafData)
    (h : ∀ (i : 𝒰.I₀), K.comap ((𝒰.pullback₁ f).f i) =
      (J.comap (𝒰.f i)).comap (𝒰.pullbackHom f i)) :
    K = J.comap f := by
  apply wholeIdeal_eq_of_openCover_comaps (𝒰.pullback₁ f)
  intro i
  calc
    K.comap ((𝒰.pullback₁ f).f i) =
        (J.comap (𝒰.f i)).comap (𝒰.pullbackHom f i) := h i
    _ = J.comap (𝒰.pullbackHom f i ≫ 𝒰.f i) :=
      (J.comap_comp (𝒰.pullbackHom f i) (𝒰.f i)).symm
    _ = J.comap ((𝒰.pullback₁ f).f i ≫ f) :=
      congrArg (fun g : (𝒰.pullback₁ f).X i ⟶ X => J.comap g) (𝒰.pullbackHom_map f i)
    _ = (J.comap f).comap ((𝒰.pullback₁ f).f i) :=
      J.comap_comp ((𝒰.pullback₁ f).f i) f

end PfaffianDescent
end
