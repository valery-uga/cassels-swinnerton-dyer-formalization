import PfaffianDescent.GrassmannianFrameProjectiveFieldPoint
import PfaffianDescent.LocalRingChartFactorization

/-!
# Equations represented by points of a projective Grassmannian chart

The existing field-point construction sends a nonzero equation in a
Grassmannian system to its projective family.  Here a field-valued point
of a local projective-frame chart is shown to represent a nonzero equation
in the corresponding homogeneous system.  This is the local reverse
incidence statement needed for the global family.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A field-valued point of a relative projective coordinate space over a
coefficient ring is the coefficient extension of a genuine field-valued
projective point, whenever its base map is the specified coefficient map. -/
theorem exists_projectiveFrameCoordinate_fieldLift
    {A F : Type u} [CommRing A] [Field F] (m : ℕ)
    (φ : A →+* F)
    (t : Spec (.of F) ⟶ projectiveFrameCoordinateSpace (R := A) m)
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) A)) =
      Spec.map (CommRingCat.ofHom φ)) :
    ∃ v : Spec (.of F) ⟶ projectiveFrameCoordinateSpace (R := F) m,
      v ≫ projectiveFrameCoordinateCoefficientMap (m := m) φ = t ∧
      v ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) F)) = 𝟙 _ := by
  let h := AllCharacteristics.HomogeneousProjective.isPullback_projectiveCoefficientMap
    φ
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) A))
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) F))
    (by simp)
  let v := h.lift t (𝟙 _) (by simpa using ht)
  exact ⟨v, h.lift_fst t (𝟙 _) (by simpa using ht),
    h.lift_snd t (𝟙 _) (by simpa using ht)⟩

/-- An arbitrary field-valued point of the glued projective-frame family
has a local Grassmannian chart and actual projective coordinates over the
field.  The chart coefficient map and both factorization equations are
retained for later equation extraction. -/
theorem exists_grassmannianFrameProjective_fieldChartLift
    {K F : Type u} [CommRing K] [Field F]
    {m n d : ℕ} (e : Fin (m + n) ≃ Monomials (Fin 4) d)
    (s : Spec (.of F) ⟶ grassmannianFrameProjectiveScheme K d e) :
    ∃ (ρ : Equiv.Perm (Fin m ⊕ Fin n))
      (t : Spec (.of F) ⟶ grassmannianFrameProjectiveChartSpace K m n)
      (φ : GrassmannianChartRing K m n →+* F)
      (v : Spec (.of F) ⟶ projectiveFrameCoordinateSpace (R := F) m),
      t ≫ grassmannianFrameProjectiveChartι K d e ρ = s ∧
      t ≫ toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) =
          Spec.map (CommRingCat.ofHom φ) ∧
      v ≫ projectiveFrameCoordinateCoefficientMap (m := m) φ = t ∧
      v ≫ toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m) F)) = 𝟙 _ := by
  obtain ⟨i, t, ht⟩ := localRing_morphism_factors_openCover F
    (grassmannianFrameProjectiveGlueData K d e).openCover s
  let ρ : Equiv.Perm (Fin m ⊕ Fin n) := i.down
  let φ : GrassmannianChartRing K m n →+* F :=
    (Spec.preimage (t ≫ toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))))).hom
  have hφ : t ≫ toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) =
      Spec.map (CommRingCat.ofHom φ) := by
    exact (Spec.map_preimage _).symm
  obtain ⟨v, hv, hvBase⟩ :=
    exists_projectiveFrameCoordinate_fieldLift m φ t hφ
  exact ⟨ρ, t, φ, v, ht, hφ, hv, hvBase⟩

section LocalChart

variable {F : Type u} [Field F] {m n d : ℕ}
  (e : Fin (m + n) ≃ Monomials (Fin 4) d)
  (ρ : Equiv.Perm (Fin m ⊕ Fin n))
  (T : Matrix (Fin n) (Fin m) F)

/-- A field-valued point of a local projective-frame family determines a
nonzero homogeneous equation in the chart's Grassmannian system, and its
ambient projective parameter classifies that equation. -/
theorem exists_grassmannianChartProjectivePoint_equation
    (t : Spec (.of F) ⟶ projectiveLinearSystemParameters (K := F) (τ := Fin m))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) F)) = 𝟙 _) :
    ∃ (p : MvPolynomial (Fin 4) F)
      (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) F d) ∈
        grassmannianChartHomogeneousSystem (R := F) d e ρ T ∧
      t ≫ homogeneousFrameToParameters d e
          (grassmannianChartHomogeneousFrame (R := F) d e ρ T)
          (grassmannianChartHomogeneousFrame_linearIndependent
            (R := F) d e ρ T) =
        projectiveClassifyingMap p hp hp0 (RingHom.id F) := by
  let q := grassmannianChartHomogeneousFrame (R := F) d e ρ T
  let hq := grassmannianChartHomogeneousFrame_linearIndependent (R := F) d e ρ T
  have ht' : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) F)) =
      Spec.map (CommRingCat.ofHom (RingHom.id F)) := by
    simpa using ht
  obtain ⟨i, g, hbase, -, hparam⟩ :=
    exists_homogeneousFrame_parameterization_eq_classifying
      d (RingHom.id F) e q hq t ht'
  let M := homogeneousFrameCoefficientMatrix d e q
  let G := polynomialQuotientGradingMap (ParameterIdeal F (Fin 4) d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) F))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
  let s := G (coordinate (ParameterIdeal F (Fin 4) d) (e i))
  let hs := G.map_mem (coordinate_mem (ParameterIdeal F (Fin 4) d) (e i))
  let p : MvPolynomial (Fin 4) F :=
    ∑ j, MvPolynomial.C (g (linearChartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) F)) s hs j)) *
      (q j).1.map (RingHom.id F)
  have hp : p.IsHomogeneous d := by
    dsimp [p]
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map (RingHom.id F)).C_mul _
  have hp0 : p ≠ 0 := homogeneousFrame_awayMap_combination_ne_zero
    d e q hq i g (RingHom.id F) hbase
  have hpSystem : (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) F d) ∈
      grassmannianChartHomogeneousSystem (R := F) d e ρ T := by
    rw [grassmannianChartHomogeneousSystem_span]
    have hqj (j : Fin m) : q j ∈ Submodule.span F (Set.range q) :=
      Submodule.subset_span ⟨j, rfl⟩
    have hpEq : (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) F d) =
        ∑ j, g (linearChartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) F)) s hs j) • q j := by
      apply Subtype.ext
      simp only [p, Submodule.coe_sum, Submodule.coe_smul,
        MvPolynomial.map_id, smul_eq_C_mul]
    rw [hpEq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hqj j)
  exact ⟨p, hp, hp0, hpSystem, hparam⟩

end LocalChart

/-- Every field-valued point of the globally glued projective-frame family
represents a nonzero homogeneous equation of its local Grassmannian chart.
The ambient projective parameter is the classifying map of that equation
after the chart coefficient map. -/
theorem exists_grassmannianFrameProjective_globalEquation
    {K F : Type u} [CommRing K] [Field F]
    {m n d : ℕ} (e : Fin (m + n) ≃ Monomials (Fin 4) d)
    (s : Spec (.of F) ⟶ grassmannianFrameProjectiveScheme K d e) :
    ∃ (ρ : Equiv.Perm (Fin m ⊕ Fin n))
      (φ : GrassmannianChartRing K m n →+* F)
      (p : MvPolynomial (Fin 4) F)
      (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      s ≫ grassmannianFrameProjectiveToGrassmannian K d e =
        Spec.map (CommRingCat.ofHom φ) ≫ grassmannianChartι K ρ ∧
      (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) F d) ∈
        grassmannianChartHomogeneousSystem (R := F) d e ρ
          ((grassmannianFrameChartUniversalMatrix K).map φ) ∧
      s ≫ grassmannianFrameProjectiveToGlobalParameters K d e =
        projectiveClassifyingMap p hp hp0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap d
            (φ.comp (algebraMap K (GrassmannianChartRing K m n))) := by
  obtain ⟨ρ, t, φ, v, ht, hφ, hv, hvBase⟩ :=
    exists_grassmannianFrameProjective_fieldChartLift e s
  let A := GrassmannianChartRing K m n
  let b : K →+* A := algebraMap K A
  let U : Matrix (Fin n) (Fin m) A := grassmannianFrameChartUniversalMatrix K
  let T : Matrix (Fin n) (Fin m) F := U.map φ
  obtain ⟨p, hp, hp0, hpSystem, hvParam⟩ :=
    exists_grassmannianChartProjectivePoint_equation e ρ T v hvBase
  have hChart : s ≫ grassmannianFrameProjectiveToGrassmannian K d e =
      Spec.map (CommRingCat.ofHom φ) ≫ grassmannianChartι K ρ := by
    rw [← ht, Category.assoc, grassmannianFrameProjectiveChartι_toGrassmannian]
    exact congrArg (fun f => f ≫ grassmannianChartι K ρ) hφ
  refine ⟨ρ, φ, p, hp, hp0, hChart, hpSystem, ?_⟩
  have hnat := grassmannianChartHomogeneousFrameToGlobalParameters_naturality
    (R := A) d b φ e ρ U
  calc
    s ≫ grassmannianFrameProjectiveToGlobalParameters K d e =
      (t ≫ grassmannianFrameProjectiveChartι K d e ρ) ≫
        grassmannianFrameProjectiveToGlobalParameters K d e := by rw [ht]
    _ = t ≫ grassmannianFrameProjectiveChartToGlobalParameters K d e ρ := by
      rw [Category.assoc, grassmannianFrameProjectiveChartι_toGlobalParameters]
    _ = (v ≫ projectiveFrameCoordinateCoefficientMap (m := m) φ) ≫
        grassmannianFrameProjectiveChartToGlobalParameters K d e ρ := by rw [hv]
    _ = v ≫
        (projectiveFrameCoordinateCoefficientMap (m := m) φ ≫
          grassmannianChartHomogeneousFrameToGlobalParameters d b e ρ U) := by
      rfl
    _ = v ≫ grassmannianChartHomogeneousFrameToGlobalParameters
          d (φ.comp b) e ρ T := by rw [hnat]
    _ = projectiveClassifyingMap p hp hp0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap d (φ.comp b) := by
      change v ≫ (homogeneousFrameToParameters d e
        (grassmannianChartHomogeneousFrame (R := F) d e ρ T)
        (grassmannianChartHomogeneousFrame_linearIndependent
          (R := F) d e ρ T) ≫
        projectiveParametersCoefficientMap d (φ.comp b)) = _
      rw [← Category.assoc, hvParam]

/-- A point of the global projective-frame family above a specified
Grassmannian quotient represents an equation in that quotient's homogeneous
linear system. -/
theorem exists_grassmannianFrameProjective_globalEquation_of_quotient
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {m n d : ℕ} (e : Fin (m + n) ≃ Monomials (Fin 4) d)
    (W : Module.Grassmannian F ((Fin m → F) × (Fin n → F)) n)
    (s : Spec (.of F) ⟶ grassmannianFrameProjectiveScheme K d e)
    (hs : s ≫ grassmannianFrameProjectiveToGrassmannian K d e =
      grassmannianQuotientMorphism K W) :
    ∃ (p : MvPolynomial (Fin 4) F)
      (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) F d) ∈
        W.toSubmodule.map
          (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).toLinearMap ∧
      s ≫ grassmannianFrameProjectiveToGlobalParameters K d e =
        projectiveClassifyingMap p hp hp0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap d (algebraMap K F) := by
  obtain ⟨ρ, φ, p, hp, hp0, hChart, hpSystem, hpParam⟩ :=
    exists_grassmannianFrameProjective_globalEquation e s
  let T : Matrix (Fin n) (Fin m) F :=
    (grassmannianFrameChartUniversalMatrix K).map φ
  have hφ : φ.comp (algebraMap K (GrassmannianChartRing K m n)) =
      algebraMap K F := by
    have hb : Spec.map (CommRingCat.ofHom φ) ≫
        grassmannianChartToBase K m n =
        Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
      calc
        Spec.map (CommRingCat.ofHom φ) ≫ grassmannianChartToBase K m n =
          Spec.map (CommRingCat.ofHom φ) ≫
            (grassmannianChartι K ρ ≫ grassmannianToBase K m n) :=
          congrArg (fun f => Spec.map (CommRingCat.ofHom φ) ≫ f)
            (grassmannianChartι_toBase K ρ).symm
        _ = (Spec.map (CommRingCat.ofHom φ) ≫ grassmannianChartι K ρ) ≫
            grassmannianToBase K m n := (Category.assoc _ _ _).symm
        _ = grassmannianQuotientMorphism K W ≫
            grassmannianToBase K m n :=
          congrArg (fun f => f ≫ grassmannianToBase K m n) (hChart.symm.trans hs)
        _ = _ := grassmannianQuotientMorphism_toBase K W
    change Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap K (GrassmannianChartRing K m n))) =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) at hb
    rw [← Spec.map_comp] at hb
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hb)
  have hEval : grassmannianChartEvaluation K T =
      Spec.map (CommRingCat.ofHom φ) := by
    have he :
        (MvPolynomial.aeval (R := K)
          (fun ij : Fin n × Fin m => T ij.1 ij.2)).toRingHom = φ := by
      apply MvPolynomial.ringHom_ext
      · intro k
        change MvPolynomial.aeval _ (MvPolynomial.C k) = φ (MvPolynomial.C k)
        rw [MvPolynomial.aeval_C]
        exact (RingHom.congr_fun hφ k).symm
      · intro ij
        exact MvPolynomial.aeval_X _ _
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he
  have hW : W = grassmannianChartQuotient F ρ T := by
    apply grassmannianQuotientAlgebraPoint_injective K
    calc
      grassmannianQuotientAlgebraPoint K W =
          grassmannianChartAlgebraPoint K F m n ρ T := by
        apply Subtype.ext
        exact hs.symm.trans (hChart.trans (by rw [← hEval]; rfl))
      _ = grassmannianQuotientAlgebraPoint K
          (grassmannianChartQuotient F ρ T) :=
        (grassmannianQuotientAlgebraPoint_chart K ρ T).symm
  refine ⟨p, hp, hp0, ?_, ?_⟩
  · rw [hW]
    exact hpSystem
  · simpa only [hφ] using hpParam

/-- The same reverse incidence statement for a point of the projective
family pulled back to a field-valued Grassmannian quotient. -/
theorem exists_grassmannianFrameProjectiveFamilyPullback_equation
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {m n d : ℕ} (e : Fin (m + n) ≃ Monomials (Fin 4) d)
    (W : Module.Grassmannian F ((Fin m → F) × (Fin n → F)) n)
    (t : Spec (.of F) ⟶ grassmannianFrameProjectiveFamilyPullback K d e
      (grassmannianQuotientMorphism K W))
    (ht : t ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
      (grassmannianQuotientMorphism K W) = 𝟙 _) :
    ∃ (p : MvPolynomial (Fin 4) F)
      (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) F d) ∈
        W.toSubmodule.map
          (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).toLinearMap ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
          (grassmannianQuotientMorphism K W) =
        projectiveClassifyingMap p hp hp0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap d (algebraMap K F) := by
  have hs : (t ≫ pullback.fst
        (grassmannianFrameProjectiveToGrassmannian K d e)
        (grassmannianQuotientMorphism K W)) ≫
        grassmannianFrameProjectiveToGrassmannian K d e =
      grassmannianQuotientMorphism K W := by
    calc
      _ = t ≫ (pullback.fst
          (grassmannianFrameProjectiveToGrassmannian K d e)
          (grassmannianQuotientMorphism K W) ≫
          grassmannianFrameProjectiveToGrassmannian K d e) :=
        Category.assoc _ _ _
      _ = t ≫ (pullback.snd
          (grassmannianFrameProjectiveToGrassmannian K d e)
          (grassmannianQuotientMorphism K W) ≫
          grassmannianQuotientMorphism K W) :=
        congrArg (fun f => t ≫ f) (pullback.condition)
      _ = (t ≫ pullback.snd
          (grassmannianFrameProjectiveToGrassmannian K d e)
          (grassmannianQuotientMorphism K W)) ≫
          grassmannianQuotientMorphism K W :=
        (Category.assoc _ _ _).symm
      _ = (𝟙 _) ≫ grassmannianQuotientMorphism K W :=
        congrArg (fun f => f ≫ grassmannianQuotientMorphism K W) ht
      _ = _ := Category.id_comp _
  obtain ⟨p, hp, hp0, hmem, hparam⟩ :=
    exists_grassmannianFrameProjective_globalEquation_of_quotient
      e W _ hs
  exact ⟨p, hp, hp0, hmem, hparam⟩

end PfaffianDescent
