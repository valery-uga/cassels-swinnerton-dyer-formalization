import PfaffianDescent.StandardChartActualNormalizedPoint
import PfaffianDescent.NormalizedIntrinsicQuadraticFieldExtension

/-! Universal field extension of the FULL quadratic series and FULL base
scheme of an arbitrary finite closed projective subscheme. The proof uses
all four actual chart algebras and the actual ambient pullback square.
It does not require any ground hyperplane avoiding the support. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Sheaf vanishing on the actual chart cover detects the entire intrinsic
system, including nilpotents on each chart. -/
theorem intrinsicFullQuadraticSystem_eq_actual_chart_cover
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [QuasiCompact i] :
    intrinsicFullQuadraticSystem i =
      ⨅ j : Fin 4, intrinsicFullQuadraticSystem
        ((finiteProjectiveStandardChartOpen i j).ι ≫ i) := by
  let C := Z.openCoverOfIsOpenCover (fun j => finiteProjectiveStandardChartOpen i j)
    (finiteProjectiveStandardChartOpen_iSup i)
  ext p
  constructor
  · intro hp
    apply (Submodule.mem_iInf _).mpr
    intro j
    exact intrinsicFullQuadraticSystem_le_comp _ i hp
  · intro hp
    have hall := (Submodule.mem_iInf _).mp hp
    refine ⟨(hall 0).1, ?_⟩
    apply (Submodule.mem_iInf _).mpr
    intro r
    change Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X r)
      (ambientChartEvaluation r p) ∈ i.ker.ideal (intrinsicQuadraticAmbientOpen r)
    rw [← i.iInf_ker_openCover_map_comp_apply C (intrinsicQuadraticAmbientOpen r)]
    apply Ideal.mem_iInf.mpr
    intro j
    exact ((Submodule.mem_iInf _).mp (hall j).2) r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ACTUAL field-base-changed embedding's full system is the joint
evaluation kernel on the tensors of the FOUR true ground chart rings.
All comparison squares are derived internally. -/
theorem canonicalProjectiveFieldBaseChangeEmbedding_intrinsic_fourTensorKernels
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    let A : Fin 4 → Type u := fun j => Γ(finiteProjectiveStandardChart i j, ⊤)
    letI : ∀ j, Algebra k (A j) := fun j => finiteProjectiveStandardChartCoefficientAlgebra i j
    letI : ∀ j, Module.Finite k (A j) := fun j => finiteProjectiveStandardChart_coefficient_finite i j
    let x : ∀ j, Fin 4 → A j := fun j r => finiteProjectiveStandardChartPolynomialRestriction i j (X r)
    intrinsicFullQuadraticSystem (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) =
      homogeneousFourChartVanishingSystem (k := K) (fun j => K ⊗[k] A j)
        (fun j r => (1 : K) ⊗ₜ[k] x j r) 2 := by
  let A : Fin 4 → Type u := fun j => Γ(finiteProjectiveStandardChart i j, ⊤)
  letI : ∀ j, Algebra k (A j) := fun j => finiteProjectiveStandardChartCoefficientAlgebra i j
  letI : ∀ j, Module.Finite k (A j) := fun j => finiteProjectiveStandardChart_coefficient_finite i j
  let x : ∀ j, Fin 4 → A j := fun j r => finiteProjectiveStandardChartPolynomialRestriction i j (X r)
  let q := canonicalProjectiveFieldBaseChangeEmbedding (K := K) i
  letI : IsClosedImmersion q := canonicalProjectiveFieldBaseChangeEmbedding_isClosedImmersion i
  rw [intrinsicFullQuadraticSystem_eq_actual_chart_cover]
  change (⨅ j : Fin 4, intrinsicFullQuadraticSystem
    ((finiteProjectiveStandardChartOpen q j).ι ≫ q)) = _
  unfold homogeneousFourChartVanishingSystem
  apply congrArg (fun f : Fin 4 → Submodule K (MvPolynomial (Fin 4) K) => ⨅ j, f j)
  funext j
  rw [← canonicalProjectiveFieldBaseChangeChartTensorIso_normalizedPoint,
    intrinsicFullQuadraticSystem_comp_isIso,
    ambientNormalizedCoordinateChartPoint_intrinsicQuadratics]

theorem intrinsicFullQuadraticSystem_actual_fieldExtension
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    intrinsicFullQuadraticSystem (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) =
      homogeneousPolynomialCoefficientSpan (K := K) (intrinsicFullQuadraticSystem i) := by
  let A : Fin 4 → Type u := fun j => Γ(finiteProjectiveStandardChart i j, ⊤)
  letI : ∀ j, Algebra k (A j) := fun j => finiteProjectiveStandardChartCoefficientAlgebra i j
  letI : ∀ j, Module.Finite k (A j) := fun j => finiteProjectiveStandardChart_coefficient_finite i j
  let x : ∀ j, Fin 4 → A j := fun j r => finiteProjectiveStandardChartPolynomialRestriction i j (X r)
  rw [canonicalProjectiveFieldBaseChangeEmbedding_intrinsic_fourTensorKernels,
    homogeneousFourChartVanishingSystem_fieldExtension,
    ← intrinsicFullQuadraticSystem_eq_actual_fourChartKernel]

theorem intrinsicFullQuadraticSystem_actual_fieldExtension_finrank
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    finrank K (intrinsicFullQuadraticSystem
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i)) =
      finrank k (intrinsicFullQuadraticSystem i) := by
  let A : Fin 4 → Type u := fun j => Γ(finiteProjectiveStandardChart i j, ⊤)
  letI : ∀ j, Algebra k (A j) := fun j => finiteProjectiveStandardChartCoefficientAlgebra i j
  letI : ∀ j, Module.Finite k (A j) := fun j => finiteProjectiveStandardChart_coefficient_finite i j
  rw [canonicalProjectiveFieldBaseChangeEmbedding_intrinsic_fourTensorKernels,
    homogeneousFourChartVanishingSystem_fieldExtension_finrank,
    ← intrinsicFullQuadraticSystem_eq_actual_fourChartKernel]

/-- Equality of the entire homogeneous base ideals, preserving the full
scheme structure rather than only the point set. -/
theorem intrinsicFullQuadraticBaseIdeal_actual_fieldExtension
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    intrinsicFullQuadraticBaseIdeal (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) =
      HomogeneousIdeal.map (ambientCoefficientGradedRingHom (algebraMap k K))
        (intrinsicFullQuadraticBaseIdeal i) := by
  apply HomogeneousIdeal.ext
  change Ideal.span (intrinsicFullQuadraticSystem
    (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) :
      Set (MvPolynomial (Fin 4) K)) = _
  rw [intrinsicFullQuadraticSystem_actual_fieldExtension]
  exact ideal_span_homogeneousPolynomialCoefficientSpan _

def intrinsicFullQuadraticBaseActualFieldExtensionIso
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    scheme (intrinsicFullQuadraticBaseIdeal
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i)) ≅
      pullback (toBase (intrinsicFullQuadraticBaseIdeal i))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  projectiveBaseChangeIso (algebraMap k K) _ _
    (by
      have h := congrArg HomogeneousIdeal.toIdeal
        (intrinsicFullQuadraticBaseIdeal_actual_fieldExtension (K := K) i)
      change (intrinsicFullQuadraticBaseIdeal
        (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i)).toIdeal =
        (intrinsicFullQuadraticBaseIdeal i).toIdeal.map
          (MvPolynomial.map (algebraMap k K)) at h
      exact h.symm)

theorem intrinsicFullQuadraticBaseActualFieldExtensionIso_toField
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    (intrinsicFullQuadraticBaseActualFieldExtensionIso (K := K) i).hom ≫
      pullback.snd _ _ = toBase (intrinsicFullQuadraticBaseIdeal
        (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i)) :=
  projectiveBaseChangeIso_hom_snd _ _ _ _

theorem intrinsicFullQuadraticBaseActualFieldExtensionIso_ambient
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    (intrinsicFullQuadraticBaseActualFieldExtensionIso (K := K) i).hom ≫
      pullback.fst _ _ ≫ quotientProjMap (intrinsicFullQuadraticBaseIdeal i) =
    quotientProjMap (intrinsicFullQuadraticBaseIdeal
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i)) ≫
      ambientCoefficientMap (algebraMap k K) := by
  rw [intrinsicFullQuadraticBaseActualFieldExtensionIso, ← Category.assoc,
    projectiveBaseChangeIso_hom_fst]
  exact projectiveCoefficientMap_comp_quotientProjMap _ _ _ _

end PfaffianDescent
