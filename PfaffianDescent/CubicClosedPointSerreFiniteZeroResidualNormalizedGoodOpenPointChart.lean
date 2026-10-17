import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedGoodOpenChartFlat
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedParameterChartRange
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualComapZeroChart
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualProjectiveLineBasicParameter

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedGoodOpen_flat_chart_at_point
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    let I := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      (hypersurfaceToBase p hp) C seed).ker
    let g := I.subschemeι ≫ projectiveLineAmbientToLine K (hypersurfaceToBase p hp)
    ∀ z : I.subscheme, g z ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen g →
      ∃ T : Scheme.{u}, ∃ j : T ⟶ I.subscheme,
        IsOpenImmersion j ∧ Flat (j ≫ g) ∧ z ∈ Set.range j := by
  let f := hypersurfaceToBase p hp
  let I := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f C seed).ker
  let π := projectiveLineAmbientToLine K f
  let g := I.subschemeι ≫ π
  let V := cubicClosedPointSerreFiniteZeroResidual_goodOpen g
  dsimp only
  intro z hz
  obtain ⟨⟨i, b⟩, x, hx⟩ :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).exists_eq (I.subschemeι z)
  change C.ι at i
  let R : CommRingCat.{u} := .of (ChartRing
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b)
  let ℓ : Spec R ⟶ projectiveLineProj K := (lineProjOpenCover K).f b
  let y : Spec R := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C (i, b) x
  have hy : ℓ y ∈ V := by
    have hc := congrArg (fun a => a x)
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine f C (i, b))
    change π ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b) x) = ℓ y at hc
    rw [← hc, hx]
    exact hz
  obtain ⟨t, ht0, w, hw, hr⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_basicParameter_inside_open ℓ V y hy
  let E := Spec (.of (Localization.Away t))
  let m : E ⟶ (lineProjOpenCover K).X b :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
  let r := m ≫ (lineProjOpenCover K).f b
  have hm : m w = y := by
    apply ℓ.isEmbedding.injective
    exact hw
  have hr' : Set.range r ⊆ V := hr
  letI : IsPrincipalIdealRing Γ(E, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_basicParameter_sections_principal t
  letI : IsDomain Γ(E, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_basicParameter_sections_domain t ht0
  let u := cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal f C (i, b) m
  let v := u ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b)
  let q := pullback.snd ((C.U i).ι ≫ f) (r ≫ projectiveLineProjToBase K)
  have hux : x ∈ Set.range u := by
    rw [cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal_range]
    exact ⟨w, hm⟩
  obtain ⟨x', hx'⟩ := hux
  have hvz : I.subschemeι z ∈ Set.range v := by
    refine ⟨x', ?_⟩
    change (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b) (u x') = I.subschemeι z
    rw [hx', hx]
  let j := cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap I v
  have hjz : z ∈ Set.range j := by
    rw [cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap_range]
    exact hvz
  have hI : I.comap v = cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal f C seed (i, b) m := by
    dsimp only [I, v, cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal]
    rw [Scheme.IdealSheafData.comap_comp,
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient_ker_comap]
  have hq : Flat ((I.comap v).subschemeι ≫ q) := by
    rw [hI]
    exact cubicClosedPointSerreFiniteZeroResidual_normalizedGoodOpenChart_flat p hp hp0 C seed (i, b) m hr'
  letI := hq
  have hv : v ≫ π = q ≫ r := by
    have hcover := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine f C (i, b)
    calc
      v ≫ π = u ≫ ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b) ≫ π) :=
        Category.assoc _ _ _
      _ = u ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C (i, b) ≫
          (lineProjOpenCover K).f b) := congrArg (fun a => u ≫ a) hcover
      _ = q ≫ r := by
        dsimp only [u, cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal,
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart]
        simp [Category.assoc, pullback.map, q, r, SerreExtensionRankTwoAffineCover.openCover]
  have hjg : j ≫ g = ((I.comap v).subschemeι ≫ q) ≫ r := by
    calc
      j ≫ g = (j ≫ I.subschemeι) ≫ π := (Category.assoc _ _ _).symm
      _ = ((I.comap v).subschemeι ≫ v) ≫ π :=
        congrArg (fun a => a ≫ π)
          (cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap_comp I v)
      _ = (I.comap v).subschemeι ≫ (v ≫ π) := Category.assoc _ _ _
      _ = (I.comap v).subschemeι ≫ (q ≫ r) :=
        congrArg (fun a => (I.comap v).subschemeι ≫ a) hv
      _ = ((I.comap v).subschemeι ≫ q) ≫ r := (Category.assoc _ _ _).symm
  refine ⟨(I.comap v).subscheme, j, inferInstance, ?_, hjz⟩
  rw [hjg]
  infer_instance

end PfaffianDescent
