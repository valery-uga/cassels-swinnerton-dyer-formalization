import PfaffianDescent.CorayAiNativeFieldChartComparison
import PfaffianDescent.CorayOriginalGenericFullJetFractionLift
import Mathlib.RingTheory.Derivation.Basic

/-! Canonical native derivation fulljet and the literal normalized native
projective chart dictionary. No rank/minor/open output is supplied.
SOURCE ONLY / HELD native fieldjet production. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A genuine K derivation gives its canonical entire fieldjet with
identity residue, retaining the actual field carrier and scalar action. -/
def derivationFieldFullJet {K F : Type u} [Field K] [Field F] [Algebra K F]
    (d : Derivation K F (Fin 2 → F)) : F →+* SurfacePlaneJet F where
  toFun := fun x => (x, d x)
  map_one' := by apply Prod.ext; rfl; exact d.map_one_eq_zero
  map_zero' := by apply Prod.ext; rfl; exact d.map_zero
  map_add' := fun x y => by apply Prod.ext; rfl; exact d.map_add x y
  map_mul' := fun x y => by
    apply Prod.ext
    · rfl
    · change d (x * y) = x • d y + MulOpposite.op y • d x
      rw [op_smul_eq_smul]
      exact d.leibniz x y

/-- Pure original coefficients in the canonical entire fieldjet. -/
theorem derivationFieldFullJet_base001 {K F : Type u} [Field K] [Field F] [Algebra K F]
    (d : Derivation K F (Fin 2 → F)) (c : K) :
    derivationFieldFullJet d (algebraMap K F c) =
      TrivSqZeroExt.inl (algebraMap K F c) := by
  apply Prod.ext
  · rfl
  · exact d.map_algebraMap c

/-- The actual normalized chart coordinate directions force the entire
canonical fieldjet to restrict to the native fulljet chart map. Chart
polynomial generation and the original K square prove the full equality. -/
theorem derivationFieldFullJet_comp_chart_eq_nativeFullJet001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* F)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K F)
    (d : Derivation K F (Fin 2 → F)) (v : Fin 2 → Fin 4 → F)
    (hcoord : ∀ i, d (g (chartCoordinate (equationIdeal p hp) j i)) = fun r => v r i)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet F))
      (surfacePlaneJetCoordinates (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v j = 1) :
    (derivationFieldFullJet d).comp g = cubicNormalizedFullJetChartMap p hp j
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v hpJ hAnchor := by
  let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
  let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  let rho := (derivationFieldFullJet d).comp g
  apply RingHom.ext
  intro a
  obtain ⟨q, rfl⟩ := eval₂_chartCoordinate_surjective (equationIdeal p hp) j a
  change rho (q.eval₂ (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j)) =
    J (q.eval₂ (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j))
  rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂]
  have hcoeff : rho.comp (chartBaseMap (equationIdeal p hp) j) =
      J.comp (chartBaseMap (equationIdeal p hp) j) := by
    apply RingHom.ext
    intro c
    change derivationFieldFullJet d (g (chartBaseMap (equationIdeal p hp) j c)) =
      J (chartBaseMap (equationIdeal p hp) j c)
    have hc : g (chartBaseMap (equationIdeal p hp) j c) = algebraMap K F c :=
      RingHom.congr_fun hBase c
    rw [hc, derivationFieldFullJet_base001, cubicNormalizedFullJetChartMap_base001]
    rfl
  have hcoordinates : (fun i => rho (chartCoordinate (equationIdeal p hp) j i)) =
      (fun i => J (chartCoordinate (equationIdeal p hp) j i)) := by
    funext i
    change derivationFieldFullJet d (g (chartCoordinate (equationIdeal p hp) j i)) =
      J (chartCoordinate (equationIdeal p hp) j i)
    rw [cubicNormalizedFullJetChartMap_coordinate001]
    apply TrivSqZeroExt.ext
    · change g (chartCoordinate (equationIdeal p hp) j i) =
        (surfacePlaneJetCoordinates z v i).fst
      simp only [surfacePlaneJetCoordinates, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, z]
    · change d (g (chartCoordinate (equationIdeal p hp) j i)) =
        (surfacePlaneJetCoordinates z v i).snd
      simpa only [surfacePlaneJetCoordinates, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] using hcoord i
  rw [hcoeff, hcoordinates]

/-- The two actual localization lifts agree after canonical fieldjet
composition. This follows from their literal original-ring restrictions. -/
theorem derivationFieldFullJet_comp_localizedLift001
    {K R F : Type u} [Field K] [CommRing R] [Field F] [Algebra K F]
    (d : Derivation K F (Fin 2 → F)) (g : R →+* F) (r : R) (hr : g r ≠ 0) :
    let J := (derivationFieldFullJet d).comp g
    let hUnit : IsUnit (J r) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hr)
    (derivationFieldFullJet d).comp
      (IsLocalization.Away.lift r (isUnit_iff_ne_zero.mpr hr) : Localization.Away r →+* F) =
      (IsLocalization.Away.lift r hUnit : Localization.Away r →+* SurfacePlaneJet F) := by
  let J := (derivationFieldFullJet d).comp g
  let hUnit : IsUnit (J r) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hr)
  apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
  rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]

/-- The SAME native projection chart's fulljet coordinate .snd is the
actual derivation of the literal normalized original field coordinate.
No minor/rank certificate is a premise; denominator nonzero is the actual
chart condition, derived internally by each original basis application. -/
theorem nativeLocalizedProjectiveChartMap_fulljet_snd_eq_normalizedDerivation001
    {K R F : Type u} [Field K] [CommRing R] [Field F] [Algebra K F]
    {σ : Type} [Fintype σ] (f : K →+* R) (x : σ → R) (a : σ)
    (g : R →+* F) (ha : g (x a) ≠ 0) (d : Derivation K F (Fin 2 → F)) (i : σ) :
    let J := (derivationFieldFullJet d).comp g
    let hUnit : IsUnit (J (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr ha)
    let mu : Localization.Away (x a) →+* SurfacePlaneJet F := IsLocalization.Away.lift (x a) hUnit
    (mu (nativeLocalizedProjectiveChartMap f x a
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a i))).snd =
      d (g (x i) / g (x a)) := by
  let J := (derivationFieldFullJet d).comp g
  let hUnit : IsUnit (J (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr ha)
  let mu : Localization.Away (x a) →+* SurfacePlaneJet F := IsLocalization.Away.lift (x a) hUnit
  let lambda : Localization.Away (x a) →+* F := IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr ha)
  have hcomp : (derivationFieldFullJet d).comp lambda = mu :=
    derivationFieldFullJet_comp_localizedLift001 d g (x a) ha
  have hfield := nativeLocalizedProjectiveChartMap_fieldLift_eq_genericChartMap001 f x a g ha
  have hc := RingHom.congr_fun hfield (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a i)
  change lambda (nativeLocalizedProjectiveChartMap f x a
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a i)) =
    projectiveEvaluationChartMap (g.comp f) (fun i => g (x i)) a ha
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a i) at hc
  rw [projectiveEvaluationChartMap_coordinate] at hc
  have hj := RingHom.congr_fun hcomp (nativeLocalizedProjectiveChartMap f x a
    (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a i))
  change derivationFieldFullJet d (lambda (nativeLocalizedProjectiveChartMap f x a
    (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a i))) =
    mu (nativeLocalizedProjectiveChartMap f x a
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a i)) at hj
  rw [hc] at hj
  exact (congrArg TrivSqZeroExt.snd hj).symm

end PfaffianDescent.Coray
end
