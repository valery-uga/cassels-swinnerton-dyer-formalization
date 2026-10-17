import PfaffianDescent.GroundTwistedCubicLiteralBinaryNineRestriction
import PfaffianDescent.QuotientChartKernel
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! SOURCE ONLY. Whole normalized equation ideals and actual affine
zero-scheme comparison under the SAME chosen twisted-cubic parametrization.
No section-action, chart equation or scheme Iso is supplied as a premise. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Ring-homomorphism composition and polynomial extensionality are
proved with ABSTRACT rings, before native chart aliases are substituted. -/
private theorem polynomialEvaluationRingHom_compCut
    {R A C : Type u} {σ : Type} [CommRing R] [CommRing A] [CommRing C]
    (e : A →+* C) (c : R →+* A) (x : σ → A)
    (v : MvPolynomial σ R →+* C)
    (hc : ∀ r, e (c r) = v (MvPolynomial.C r))
    (hx : ∀ i, e (x i) = v (X i)) (F : MvPolynomial σ R) :
    e (F.eval₂ c x) = v F := by
  have h : e.comp (eval₂Hom c x) = v := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, eval₂Hom_C] using hc r
    · intro i
      simpa only [RingHom.comp_apply, eval₂Hom_X'] using hx i
  exact DFunLike.congr_fun h F

/-- Literal substitution evaluated in an ABSTRACT coefficient ring. -/
private def literalBinaryEvaluationHom
    {T : Type u} [CommRing T] (c : K →+* T) (x : Bool → T) :
    MvPolynomial (Fin 4) K →+* T :=
  (eval₂Hom c x).comp
    ((rename finTwoEquiv).comp (standardTwistedCubicParam K)).toRingHom

private theorem literalBinaryEvaluationHom_C
    {T : Type u} [CommRing T] (c : K →+* T) (x : Bool → T) (r : K) :
    literalBinaryEvaluationHom c x (C r) = c r := by
  simp [literalBinaryEvaluationHom, standardTwistedCubicParam]

private theorem literalBinaryEvaluationHom_X
    {T : Type u} [CommRing T] (c : K →+* T) (x : Bool → T)
    (b : Bool) (hself : x b = 1) (i : Fin 4) :
    literalBinaryEvaluationHom c x (X i) =
      (if b then (![x false ^ 3, x false ^ 2, x false, 1] : Fin 4 → T) i
       else (![1, x true, x true ^ 2, x true ^ 3] : Fin 4 → T) i) := by
  cases b <;> fin_cases i <;>
    simp [literalBinaryEvaluationHom, standardTwistedCubicParam, finTwoEquiv, hself]

private theorem nativeChartCoefficientMap_baseCut (b : Bool) (r : K) :
    standardTwistedCubicNativeChartCoefficientMap (K := K) b
      (chartBaseMap I (if b then 3 else 0) r) = chartBaseMap L b r := by
  cases b
  · exact standardTwistedCubicChartZeroToLineChart_base (K := K) r
  · exact standardTwistedCubicChartThreeToLineChart_base (K := K) r

private theorem nativeChartCoefficientMap_coordinateCut (b : Bool) (i : Fin 4) :
    standardTwistedCubicNativeChartCoefficientMap (K := K) b
      (chartCoordinate I (if b then 3 else 0) i) =
      (if b then
        (![chartCoordinate L b false ^ 3, chartCoordinate L b false ^ 2,
          chartCoordinate L b false, 1] : Fin 4 → ChartRing L b) i
       else
        (![1, chartCoordinate L b true, chartCoordinate L b true ^ 2,
          chartCoordinate L b true ^ 3] : Fin 4 → ChartRing L b) i) := by
  cases b
  · exact standardTwistedCubicChartZeroToLineChart_coordinate (K := K) i
  · exact standardTwistedCubicChartThreeToLineChart_coordinate (K := K) i

/-- Arbitrary polynomial evaluation commutes with the ACTUAL native chart
coefficient map, not merely the four coordinate evaluations. -/
theorem standardTwistedCubicNativeChartCoefficientMap_literalPolynomial
    (b : Bool) (F : MvPolynomial (Fin 4) K) :
    standardTwistedCubicNativeChartCoefficientMap (K := K) b
        (F.eval₂ (chartBaseMap I (if b then 3 else 0))
          (chartCoordinate I (if b then 3 else 0))) =
      (rename finTwoEquiv (standardTwistedCubicParam K F)).eval₂
        (chartBaseMap L b) (chartCoordinate L b) := by
  exact polynomialEvaluationRingHom_compCut
    (standardTwistedCubicNativeChartCoefficientMap (K := K) b)
    (chartBaseMap I (if b then 3 else 0)) (chartCoordinate I (if b then 3 else 0))
    (literalBinaryEvaluationHom (chartBaseMap L b) (chartCoordinate L b))
    (fun r => (nativeChartCoefficientMap_baseCut b r).trans
      (literalBinaryEvaluationHom_C (chartBaseMap L b) (chartCoordinate L b) r).symm)
    (fun i => (nativeChartCoefficientMap_coordinateCut b i).trans
      (literalBinaryEvaluationHom_X (chartBaseMap L b) (chartCoordinate L b)
        b (chartCoordinate_self L b) i).symm) F

/-- The whole original curve-to-intersection chart kernel maps to the
whole binary hypersurface chart kernel. This retains nonreduced equations. -/
theorem standardTwistedCubicNativeChartCoefficientMap_restrictedEquationKernel
    (b : Bool) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    let G := rename finTwoEquiv (standardTwistedCubicParam K F)
    let hG : G.IsHomogeneous 9 := by
      simpa only [Nat.reduceMul] using
        (standardTwistedCubicParam_homogeneous hF).rename_isHomogeneous (f := finTwoEquiv)
    (RingHom.ker (chartQuotientMap I (I ⊔ equationIdeal F hF)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)
      (if b then 3 else 0))).map
        (standardTwistedCubicNativeChartCoefficientMap (K := K) b) =
      RingHom.ker (chartQuotientMap L (equationIdeal G hG) (by exact bot_le) b) := by
  dsimp only
  rw [chartQuotientMap_ker_eq_equation, Ideal.map_span, Set.image_singleton,
    standardTwistedCubicNativeChartCoefficientMap_literalPolynomial]
  symm
  apply chartQuotientMap_ker_eq_principal_of_ideal_eq_sup
  simp only [HomogeneousIdeal.toIdeal_bot, bot_sup_eq]
  rfl

/-- Abstract chart inverse cut. All cancellation occurs before any large
homogeneous chart or actual global scheme Iso is substituted. -/
private def chartIsoFromActualGlobalIsoCut
    {X Y U V : Scheme.{u}} (e : X ≅ Y)
    (i : U ⟶ X) (j : V ⟶ Y) [Mono i] [Mono j]
    (f : U ⟶ V) (g : V ⟶ U)
    (hf : i ≫ e.hom = f ≫ j) (hg : j ≫ e.inv = g ≫ i) : U ≅ V where
  hom := f
  inv := g
  hom_inv_id := by
    apply (cancel_mono i).mp
    calc
      (f ≫ g) ≫ i = f ≫ (j ≫ e.inv) := by rw [Category.assoc, ← hg]
      _ = (i ≫ e.hom) ≫ e.inv := by rw [← Category.assoc, ← hf]
      _ = (𝟙 U) ≫ i := by simp
  inv_hom_id := by
    apply (cancel_mono j).mp
    calc
      (g ≫ f) ≫ j = g ≫ (i ≫ e.hom) := by rw [Category.assoc, ← hf]
      _ = (j ≫ e.inv) ≫ e.hom := by rw [← Category.assoc, ← hg]
      _ = (𝟙 V) ≫ j := by simp

/-- Reflect the PROVED Spec-map instance explicitly, while its ring-map
argument is abstract; instance search need not unfold the Spec.map alias. -/
private theorem ringMapBijective_of_specMapIsIsoCut
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (h : IsIso (Spec.map (CommRingCat.ofHom f))) : Function.Bijective f := by
  have hop : IsIso (CommRingCat.ofHom f).op :=
    @isIso_of_reflects_iso _ _ _ _ _ _
      (CommRingCat.ofHom f).op Scheme.Spec h inferInstance
  have hring : IsIso (CommRingCat.ofHom f) :=
    @isIso_of_op _ _ _ _ (CommRingCat.ofHom f) hop
  exact (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom f)).mp hring

private theorem nativeChartCoefficientMap_bijectiveCut (b : Bool) :
    Function.Bijective (standardTwistedCubicNativeChartCoefficientMap (K := K) b) := by
  let f := standardTwistedCubicNativeChartCoefficientMap (K := K) b
  have hIso : IsIso (Spec.map (CommRingCat.ofHom f)) := by
    cases b
    · exact (chartIsoFromActualGlobalIsoCut
        (standardTwistedCubicProjectiveLineIso (K := K)).symm
        (chartι L false) (chartι I 0)
        (Spec.map (CommRingCat.ofHom (standardTwistedCubicChartZeroToLineChart (K := K))))
        (Spec.map (CommRingCat.ofHom (lineChartToStandardTwistedCubicChartZero (K := K))))
        (standardProjectiveLineChartZero_toTwistedCubic (K := K))
        (standardTwistedCubicChartZero_toProjectiveLine (K := K))).isIso_hom
    · exact (chartIsoFromActualGlobalIsoCut
        (standardTwistedCubicProjectiveLineIso (K := K)).symm
        (chartι L true) (chartι I 3)
        (Spec.map (CommRingCat.ofHom (standardTwistedCubicChartThreeToLineChart (K := K))))
        (Spec.map (CommRingCat.ofHom (lineChartToStandardTwistedCubicChartThree (K := K))))
        (standardProjectiveLineChartThree_toTwistedCubic (K := K))
        (standardTwistedCubicChartThree_toProjectiveLine (K := K))).isIso_hom
  exact ringMapBijective_of_specMapIsIsoCut f hIso

private def nativeChartCoefficientRingEquiv (b : Bool) :
    ChartRing I (if b then 3 else 0) ≃+* ChartRing L b :=
  RingEquiv.ofBijective (standardTwistedCubicNativeChartCoefficientMap (K := K) b)
    (nativeChartCoefficientMap_bijectiveCut b)

private theorem nativeChartCoefficientRingEquiv_coeCut (b : Bool) :
    (nativeChartCoefficientRingEquiv (K := K) b :
      ChartRing I (if b then 3 else 0) →+* ChartRing L b) =
        standardTwistedCubicNativeChartCoefficientMap (K := K) b := rfl

/-- Abstract quotient comparison from a PROVED whole-kernel image equality. -/
private def nativeEquationQuotientRingEquivCut
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (e : A ≃+* B) (f : A →+* C) (g : B →+* D)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : (RingHom.ker f).map (e : A →+* B) = RingHom.ker g) : C ≃+* D :=
  (RingHom.quotientKerEquivOfSurjective hf).symm.trans
    ((Ideal.quotientEquiv (RingHom.ker f) (RingHom.ker g) e hk.symm).trans
      (RingHom.quotientKerEquivOfSurjective hg))

private theorem nativeEquationQuotientRingEquivCut_apply
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (e : A ≃+* B) (f : A →+* C) (g : B →+* D)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : (RingHom.ker f).map (e : A →+* B) = RingHom.ker g) (x : A) :
    nativeEquationQuotientRingEquivCut e f g hf hg hk (f x) = g (e x) := by
  change (RingHom.quotientKerEquivOfSurjective hg)
    (Ideal.quotientEquiv (RingHom.ker f) (RingHom.ker g) e hk.symm
      ((RingHom.quotientKerEquivOfSurjective hf).symm (f x))) = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply,
    Ideal.quotientEquiv_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Specialize the proved ENTIRE equation-kernel image with the exact
native RingEquiv coercion, then reuse this SAME explicit witness. -/
private theorem nativeChosenRestrictedEquationKernelWitness
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool) :
    let A : GL (Fin 4) K := Classical.choose hB
    let F' := linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F
    let hF' := linearSubstitution_homogeneous (A : Matrix (Fin 4) (Fin 4) K) hF
    let G := hB.literalRestrictedBinaryNine F hF
    (RingHom.ker (chartQuotientMap I (I ⊔ equationIdeal F' hF')
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) (if b then 3 else 0))).map
        (nativeChartCoefficientRingEquiv (K := K) b :
          ChartRing I (if b then 3 else 0) →+* ChartRing L b) =
      RingHom.ker (chartQuotientMap L
        (equationIdeal (G : MvPolynomial Bool K) G.property) (by exact bot_le) b) := by
  dsimp only
  rw [nativeChartCoefficientRingEquiv_coeCut]
  exact standardTwistedCubicNativeChartCoefficientMap_restrictedEquationKernel b _ _

/-- Affine zero-scheme ring comparison for ORIGINAL ground F, using
EXACTLY the SAME chosen matrix and literal restricted binary polynomial. -/
def GroundTwistedCubicPresentation.literalBinaryNineNativeChartRingEquiv
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool) :
    let A : GL (Fin 4) K := Classical.choose hB
    let F' := linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F
    let hF' := linearSubstitution_homogeneous (A : Matrix (Fin 4) (Fin 4) K) hF
    let G := hB.literalRestrictedBinaryNine F hF
    ChartRing (I ⊔ equationIdeal F' hF') (if b then 3 else 0) ≃+*
      ChartRing (equationIdeal (G : MvPolynomial Bool K) G.property) b := by
  dsimp only
  apply nativeEquationQuotientRingEquivCut
    (nativeChartCoefficientRingEquiv (K := K) b)
    (chartQuotientMap I _ (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) _)
    (chartQuotientMap L _ (by exact bot_le) b)
    (chartQuotientMap_surjective _ _ _ _)
    (chartQuotientMap_surjective _ _ _ _)
  exact nativeChosenRestrictedEquationKernelWitness hB F hF b

/-- Exact comparison with the actual chart projection to the curve,
before passing to spectra; there is no newly chosen quotient map. -/
theorem GroundTwistedCubicPresentation.literalBinaryNineNativeChartRingEquiv_projection
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool)
    (x : ChartRing I (if b then 3 else 0)) :
    let A : GL (Fin 4) K := Classical.choose hB
    let F' := linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F
    let hF' := linearSubstitution_homogeneous (A : Matrix (Fin 4) (Fin 4) K) hF
    let G := hB.literalRestrictedBinaryNine F hF
    hB.literalBinaryNineNativeChartRingEquiv F hF b
      (chartQuotientMap I (I ⊔ equationIdeal F' hF')
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) _ x) =
      chartQuotientMap L (equationIdeal (G : MvPolynomial Bool K) G.property)
        (by exact bot_le) b
        (standardTwistedCubicNativeChartCoefficientMap (K := K) b x) := by
  exact nativeEquationQuotientRingEquivCut_apply
    (nativeChartCoefficientRingEquiv (K := K) b)
    (chartQuotientMap I _ (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) _)
    (chartQuotientMap L _ (by exact bot_le) b)
    (chartQuotientMap_surjective _ _ _ _)
    (chartQuotientMap_surjective _ _ _ _)
    (nativeChosenRestrictedEquationKernelWitness hB F hF b) x

/-- Actual binary hypersurface chart is Iso to the original transformed
WHOLE intersection chart, with its nilpotent scheme structure retained. -/
def GroundTwistedCubicPresentation.literalBinaryNineNativeChartIso
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool) :
    let A : GL (Fin 4) K := Classical.choose hB
    let F' := linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F
    let hF' := linearSubstitution_homogeneous (A : Matrix (Fin 4) (Fin 4) K) hF
    let G := hB.literalRestrictedBinaryNine F hF
    Spec (.of (ChartRing (equationIdeal (G : MvPolynomial Bool K) G.property) b)) ≅
      Spec (.of (ChartRing (I ⊔ equationIdeal F' hF') (if b then 3 else 0))) :=
  Scheme.Spec.mapIso (hB.literalBinaryNineNativeChartRingEquiv F hF b).toCommRingCatIso.op

/-- The affine scheme Iso preserves the ORIGINAL zero-scheme projection
followed by the SAME native chart parametrization to the original curve. -/
theorem GroundTwistedCubicPresentation.literalBinaryNineNativeChartIso_projection
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool) :
    let A : GL (Fin 4) K := Classical.choose hB
    let F' := linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F
    let hF' := linearSubstitution_homogeneous (A : Matrix (Fin 4) (Fin 4) K) hF
    let G := hB.literalRestrictedBinaryNine F hF
    (hB.literalBinaryNineNativeChartIso F hF b).hom ≫
        Spec.map (CommRingCat.ofHom (chartQuotientMap I (I ⊔ equationIdeal F' hF')
          (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) (if b then 3 else 0))) =
      Spec.map (CommRingCat.ofHom (chartQuotientMap L
        (equationIdeal (G : MvPolynomial Bool K) G.property) (by exact bot_le) b)) ≫
        standardTwistedCubicNativeChartMorphism (K := K) b := by
  dsimp only
  change Spec.map (CommRingCat.ofHom
      (hB.literalBinaryNineNativeChartRingEquiv F hF b).toRingHom) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    standardTwistedCubicNativeChartMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact hB.literalBinaryNineNativeChartRingEquiv_projection F hF b x

end PfaffianDescent.QuarticNet
