import AllCharacteristics.UniversalAffineSourceIso
import AllCharacteristics.ProjectiveDominanceOfHomogeneousRelations
import AllCharacteristics.FunctionFieldChartDominance

/-!
# The actual affine source of the universal secant construction

The polynomial vector descended to the generic line field is evaluated in
the function field of the actual nine-variable affine source.  This module
retains the ground-field coefficient map and turns polynomial homogeneous
relation detection into unirationality of the actual projective scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] affineSourceAlgebra affineSourceFractionRing

/-- The coefficient map from the original ground field into the localized
universal parameter ring. -/
def kollarUniversalLocalizedCoefficientMap (k : Type u) [Field k] :
    k →+* KollarUniversalLocalizedParameterRing k :=
  (MvPolynomial.C : FractionRing (MvPolynomial (Fin 3) k) →+*
    KollarUniversalLocalizedParameterRing k).comp
      ((algebraMap (MvPolynomial (Fin 3) k)
        (FractionRing (MvPolynomial (Fin 3) k))).comp MvPolynomial.C)

set_option backward.isDefEq.respectTransparency.types false in
/-- The localized polynomial ring embeds in the actual source function
field, and its original-field coefficients agree with the source structure
morphism at the generic point. -/
theorem exists_kollarUniversalParameterEvaluation (k : Type u) [Field k] :
    ∃ f : KollarUniversalLocalizedParameterRing k →+*
        (Spec (.of (KollarUniversalParameterRing k))).functionField,
      Function.Injective f ∧
      Spec.map (CommRingCat.ofHom
        (f.comp (kollarUniversalLocalizedCoefficientMap k))) =
          (Spec (.of (KollarUniversalParameterRing k))).fromSpecStalk
            (genericPoint (Spec (.of (KollarUniversalParameterRing k)))) ≫
              kollarUniversalSourceToBase k := by
  obtain ⟨f, hf, hfrac⟩ := exists_kollarUniversalLocalizedParameterMap k
  letI : Algebra (KollarUniversalLocalizedParameterRing k)
      (Spec (.of (KollarUniversalParameterRing k))).functionField := f.toAlgebra
  obtain ⟨htower, hfield⟩ := hfrac
  letI := htower
  letI := hfield
  have hfinj : Function.Injective f :=
    IsFractionRing.injective (KollarUniversalLocalizedParameterRing k)
      (Spec (.of (KollarUniversalParameterRing k))).functionField
  let c : k →+* KollarUniversalParameterRing k :=
    (MvPolynomial.C : MvPolynomial (Fin 3) k →+*
      KollarUniversalParameterRing k).comp MvPolynomial.C
  have hcoeff : (algebraMap (KollarUniversalParameterRing k)
      (KollarUniversalLocalizedParameterRing k)).comp c =
        kollarUniversalLocalizedCoefficientMap k := by
    ext r
    simp only [c, kollarUniversalLocalizedCoefficientMap, RingHom.comp_apply,
      MvPolynomial.algebraMap_def, MvPolynomial.map_C]
  have hbase : f.comp (kollarUniversalLocalizedCoefficientMap k) =
      (algebraMap (KollarUniversalParameterRing k)
        (Spec (.of (KollarUniversalParameterRing k))).functionField).comp c := by
    rw [← hcoeff]
    exact congrArg (fun g => g.comp c) hf
  refine ⟨f, hfinj, ?_⟩
  calc
    _ = Spec.map (CommRingCat.ofHom
        ((algebraMap (KollarUniversalParameterRing k)
          (Spec (.of (KollarUniversalParameterRing k))).functionField).comp c)) :=
      congrArg (fun g : k →+* (Spec (.of (KollarUniversalParameterRing k))).functionField =>
        Spec.map (CommRingCat.ofHom g)) hbase
    _ = _ := kollarUniversalSource_functionField_baseMap k

namespace HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- Homogeneous relation detection for the descended polynomial vector gives
an actual dominant point over the actual universal source function field. -/
theorem kollarUniversalSource_dominant_point_of_homogeneous_relations
    {k : Type u} [Field k] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    [IrreducibleSpace (scheme I)]
    (R : σ → KollarUniversalLocalizedParameterRing k) (hR : R ≠ 0)
    (he : ∀ p : MvPolynomial σ k, p ∈ I.toIdeal →
      p.eval₂ (kollarUniversalLocalizedCoefficientMap k) R = 0)
    (hdetect : ∀ (p : MvPolynomial σ k) (d : ℕ), p.IsHomogeneous d →
      p.eval₂ (kollarUniversalLocalizedCoefficientMap k) R = 0 → p ∈ I.toIdeal) :
    ∃ q : Spec (Spec (.of (KollarUniversalParameterRing k))).functionField ⟶ scheme I,
      q ≫ toBase I =
        (Spec (.of (KollarUniversalParameterRing k))).fromSpecStalk
          (genericPoint (Spec (.of (KollarUniversalParameterRing k)))) ≫
            kollarUniversalSourceToBase k ∧ IsDominant q := by
  classical
  obtain ⟨f, hfinj, hfbase⟩ := exists_kollarUniversalParameterEvaluation k
  let E : MvPolynomial σ k →+*
      (Spec (.of (KollarUniversalParameterRing k))).functionField :=
    f.comp (MvPolynomial.eval₂Hom (kollarUniversalLocalizedCoefficientMap k) R)
  have hEe : ∀ p : MvPolynomial σ k, p ∈ I.toIdeal → E p = 0 := by
    intro p hp
    change f (p.eval₂ (kollarUniversalLocalizedCoefficientMap k) R) = 0
    rw [he p hp, map_zero]
  have hEdetect : ∀ (p : MvPolynomial σ k) (d : ℕ),
      p.IsHomogeneous d → E p = 0 → p ∈ I.toIdeal := by
    intro p d hp hz
    change f (p.eval₂ (kollarUniversalLocalizedCoefficientMap k) R) = 0 at hz
    apply hdetect p d hp
    apply hfinj
    change f (p.eval₂ (kollarUniversalLocalizedCoefficientMap k) R) = f 0
    simpa only [map_zero] using hz
  obtain ⟨j, hj⟩ : ∃ j, R j ≠ 0 := by
    by_contra h
    push Not at h
    exact hR (funext h)
  have hEj : E (MvPolynomial.X j) ≠ 0 := by
    dsimp only [E, RingHom.comp_apply]
    rw [MvPolynomial.eval₂Hom_X']
    exact fun hz => hj (hfinj (hz.trans (map_zero f).symm))
  obtain ⟨q, hqbase, hqdom⟩ :=
    exists_dominant_projective_point_of_homogeneous_relations I E hEe hEdetect j hEj
  have hEbase : E.comp MvPolynomial.C =
      f.comp (kollarUniversalLocalizedCoefficientMap k) := by
    ext r
    exact congrArg f (MvPolynomial.eval₂Hom_C
      (kollarUniversalLocalizedCoefficientMap k) R r)
  refine ⟨q, ?_, hqdom⟩
  exact hqbase.trans ((congrArg
    (fun g : k →+* (Spec (.of (KollarUniversalParameterRing k))).functionField =>
      Spec.map (CommRingCat.ofHom g)) hEbase).trans hfbase)

set_option backward.isDefEq.respectTransparency.types false in
/-- A descended universal polynomial vector detecting the target's
homogeneous relations proves unirationality over the original field. -/
theorem isUnirationalOver_of_kollarUniversalPolynomial_homogeneous_relations
    {k : Type u} [Field k] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    [IrreducibleSpace (scheme I)]
    (R : σ → KollarUniversalLocalizedParameterRing k) (hR : R ≠ 0)
    (he : ∀ p : MvPolynomial σ k, p ∈ I.toIdeal →
      p.eval₂ (kollarUniversalLocalizedCoefficientMap k) R = 0)
    (hdetect : ∀ (p : MvPolynomial σ k) (d : ℕ), p.IsHomogeneous d →
      p.eval₂ (kollarUniversalLocalizedCoefficientMap k) R = 0 → p ∈ I.toIdeal) :
    IsUnirationalOver k (scheme I) (toBase I) := by
  obtain ⟨q, hqbase, hqdom⟩ :=
    kollarUniversalSource_dominant_point_of_homogeneous_relations I R hR he hdetect
  exact isUnirationalOver_of_affineIso_genericFieldPoint
    (kollarUniversalSourceToBase k) (toBase I) 9
    (kollarUniversalSourceAffineIso k) (kollarUniversalSourceAffineIso_over k)
    q hqbase ((Scheme.Hom.isDominant_iff_genericPoint_eq q).mp hqdom)

/-- The hypersurface form needs only the actual defining equation at the
descended vector; every other equation in its principal ideal follows. -/
theorem isUnirationalOver_hypersurface_of_kollarUniversalPolynomial
    {k : Type u} [Field k] {σ : Type} [Finite σ]
    (F : MvPolynomial σ k) {d : ℕ} (hF : F.IsHomogeneous d)
    [IrreducibleSpace (hypersurface F hF)]
    (R : σ → KollarUniversalLocalizedParameterRing k) (hR : R ≠ 0)
    (he : F.eval₂ (kollarUniversalLocalizedCoefficientMap k) R = 0)
    (hdetect : ∀ (p : MvPolynomial σ k) (e : ℕ), p.IsHomogeneous e →
      p.eval₂ (kollarUniversalLocalizedCoefficientMap k) R = 0 →
        p ∈ Ideal.span ({F} : Set (MvPolynomial σ k))) :
    IsUnirationalOver k (hypersurface F hF) (hypersurfaceToBase F hF) := by
  letI : IrreducibleSpace (scheme (equationIdeal F hF)) := by
    change IrreducibleSpace (hypersurface F hF)
    infer_instance
  have hker : (equationIdeal F hF).toIdeal ≤
      RingHom.ker (MvPolynomial.eval₂Hom (kollarUniversalLocalizedCoefficientMap k) R) := by
    change Ideal.span {F} ≤ _
    rw [Ideal.span_singleton_le_iff_mem]
    exact he
  change IsUnirationalOver k (scheme (equationIdeal F hF)) (toBase (equationIdeal F hF))
  exact isUnirationalOver_of_kollarUniversalPolynomial_homogeneous_relations
    (equationIdeal F hF) R hR (fun p hp => hker hp) hdetect

end HomogeneousProjective
end AllCharacteristics
