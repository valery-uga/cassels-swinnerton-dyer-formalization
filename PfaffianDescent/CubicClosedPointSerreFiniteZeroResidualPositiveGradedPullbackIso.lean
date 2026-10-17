import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullback
import PfaffianDescent.VoisinProjectiveSpaceCech

/-! # Actual pullback identifies intrinsic negative twists

For standard graded rings the actual graded restriction adjunct is an
isomorphism. The proof uses the actual homogeneous-multiplication square
and coordinate-open invertibility, rather than retaining an identification.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

variable {A B ρ τ : Type u} [CommRing A] [CommRing B]
  [SetLike ρ A] [AddSubgroupClass ρ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒢 : ℕ → ρ) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]
  (f : 𝒢 →+*ᵍ ℋ)
  (hf : HomogeneousIdeal.irrelevant ℋ ≤ (HomogeneousIdeal.irrelevant 𝒢).map f)

/-- Actual pullback along a standard graded map identifies all intrinsic
negative twists. The only ring conditions are degree-one generation. -/
theorem cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_isIso
    (h𝒢 : (HomogeneousIdeal.irrelevant 𝒢).toIdeal ≤
      Ideal.span (Set.range (fun s : 𝒢 1 => (s : A))))
    (hℋ : (HomogeneousIdeal.irrelevant ℋ).toIdeal ≤
      Ideal.span (Set.range (fun s : ℋ 1 => (s : B)))) (m : ℕ) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf m) := by
  let g := Proj.map f hf
  let P := Scheme.Modules.pullback g
  let V : 𝒢 1 → (Proj ℋ).Opens :=
    fun s => g ⁻¹ᵁ homogeneousBasicOpen 𝒢 (s : A)
  have hV : IsOpenCover V := by
    apply IsOpenCover.mk
    change ⨆ s : 𝒢 1, (Opens.map g.base).obj
      (homogeneousBasicOpen 𝒢 (s : A)) = ⊤
    calc
      _ = (Opens.map g.base).obj (⨆ s : 𝒢 1, homogeneousBasicOpen 𝒢 (s : A)) :=
        (Opens.map_iSup g.base (fun s : 𝒢 1 => homogeneousBasicOpen 𝒢 (s : A))).symm
      _ = (Opens.map g.base).obj ⊤ := congrArg (Opens.map g.base).obj
        (Proj.iSup_basicOpen_eq_top 𝒢 (fun s : 𝒢 1 => (s : A)) h𝒢)
      _ = ⊤ := rfl
  induction m with
  | zero => exact cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_zero_isIso 𝒢 ℋ f hf
  | succ m ih =>
    letI := ih
    apply schemeModule_isIso_of_openCover_restrict_isIso
      ((Proj ℋ).openCoverOfIsOpenCover V hV)
    intro s
    change 𝒢 1 at s
    let R := Scheme.Modules.restrictFunctor (V s).ι
    change IsIso (R.map
      (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf (m + 1)))
    let s' : ℋ 1 := ⟨f s, f.2 s.2⟩
    letI : IsIso ((Scheme.Modules.restrictFunctor
        (homogeneousBasicOpen 𝒢 (s : A)).ι).map (positiveMulHomogeneous 𝒢 s m)) :=
      restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝒢 s m h𝒢
    letI : IsIso (R.map (P.map (positiveMulHomogeneous 𝒢 s m))) :=
      cubicPointTraceFieldBaseChangePullbackRestrict_map_isIso g
        (homogeneousBasicOpen 𝒢 (s : A)) (positiveMulHomogeneous 𝒢 s m)
    letI : IsIso (R.map (positiveMulHomogeneous ℋ s' m)) :=
      restrict_positiveMulHomogeneous_isIso_on_basicOpen ℋ s' m hℋ
    haveI : IsIso (R.map (P.map (positiveMulHomogeneous 𝒢 s m)) ≫
        R.map (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf (m+1))) := by
      rw [← R.map_comp, cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_mul,
        R.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_left (R.map (P.map (positiveMulHomogeneous 𝒢 s m))) _

/-- The resulting identification is the actual graded restriction adjunct. -/
def cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackIso
    (h𝒢 : (HomogeneousIdeal.irrelevant 𝒢).toIdeal ≤
      Ideal.span (Set.range (fun s : 𝒢 1 => (s : A))))
    (hℋ : (HomogeneousIdeal.irrelevant ℋ).toIdeal ≤
      Ideal.span (Set.range (fun s : ℋ 1 => (s : B)))) (m : ℕ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (positiveSheafOfModules 𝒢 m) ≅
      positiveSheafOfModules ℋ m := by
  letI := cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_isIso 𝒢 ℋ f hf h𝒢 hℋ m
  exact asIso (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf m)

end PfaffianDescent.ProjectiveNegativeTwist
