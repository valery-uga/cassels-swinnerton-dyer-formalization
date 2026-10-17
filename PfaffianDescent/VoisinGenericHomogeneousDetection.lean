import PfaffianDescent.VoisinGenericQuadraticDetection

/-!
# Detecting a homogeneous frame by generic marked points

The finite-incidence contradiction used for eight quadrics works for an
arbitrary degree and independent homogeneous frame.  In particular it can
detect sixteen cubic sections on the generic sixteen-point configuration.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- No nonzero member of an independent homogeneous frame has simultaneous
incidence lifts at the sixteen labeled points of an ordered configuration. -/
def HomogeneousSixteenNoCommonResidueFieldEquationAt
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    {d n m : ℕ} (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left) : Prop :=
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let T := projectiveLinearSystemParameters (K := K) (τ := Fin n)
  let tBase := toBase
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
  let marked := fun i =>
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 16
      (hypersurfaceToAmbient cubic hcubic) i
  let frameMap := homogeneousFrameToParameters d e frame hframe
  ¬ ∃ (t : Spec (.of (O.residueField z)) ⟶ T)
    (q : Fin 16 → (Spec (.of (O.residueField z)) ⟶
      projectiveUniversalFamily K (Fin 4) d))
    (hbase : O.fromSpecResidueField z ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).hom = t ≫ tBase),
    ∀ i, q i ≫ projectiveUniversalIncidence K (Fin 4) d =
      pullback.lift (O.fromSpecResidueField z) t hbase ≫
        projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) d
          (orderedFamilyConfigurationOver
            (hypersurfaceToBase cubic hcubic) 16).hom
          tBase marked frameMap i

/-- If a marked sixteen-point configuration avoids the finite incidence of
an independent degree-`d` frame, no nonzero coefficient vector in that frame
can vanish at all sixteen marked points after base change. -/
theorem homogeneousFrame_detected_of_noCommonIncidence_sixteen
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    {d n m : ℕ}
    (a : K →+* Q) (b : Q →+* L) (hb : algebraMap Q L = b)
    (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame)
    {X : Scheme.{u}}
    (xBase : X ⟶ Spec (.of K))
    (marked : Fin 16 → (X ⟶ Proj (homogeneousSubmodule (Fin 4) K)))
    (r : Spec (.of L) ⟶ X)
    (hrBase : r ≫ xBase = Spec.map (CommRingCat.ofHom (b.comp a)))
    (x : Fin 4 → A)
    (he : ∀ q ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q)).toIdeal,
      (eval₂Hom (algebraMap Q A) x) q = 0)
    (ell : MvPolynomial (Fin 4) Q) (hell : ell.IsHomogeneous 1)
    (hellOne : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal
      (eval₂Hom (algebraMap Q A) x) he)
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q)).toIdeal ell) = 1)
    (φ : Fin 16 → A →ₐ[Q] L)
    (hmarked : ∀ i,
      Spec.map (CommRingCat.ofHom (φ i).toRingHom) ≫
          linearNormalizedPointAt
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
            x he
            (Ideal.Quotient.mk
              (⊥ : HomogeneousIdeal
                (homogeneousSubmodule (Fin 4) Q)).toIdeal ell)
            (polynomial_class_mem_grading
              (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
              ell hell) hellOne ≫
          quotientProjMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)) ≫
          ambientCoefficientMap a = r ≫ marked i)
    (hno : ¬ ∃ (t : Spec (.of L) ⟶
        projectiveLinearSystemParameters (K := K) (τ := Fin n))
      (q : Fin 16 → (Spec (.of L) ⟶
        projectiveUniversalFamily K (Fin 4) d))
      (hbase : r ≫ xBase = t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))),
      ∀ i, q i ≫ projectiveUniversalIncidence K (Fin 4) d =
        pullback.lift r t hbase ≫
          projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) d
            xBase
            (toBase
              (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
            marked (homogeneousFrameToParameters d e frame hframe) i) :
    ∀ c : Fin n → Q,
      (∀ i, MvPolynomial.eval₂ (algebraMap Q L)
        (fun j => φ i (x j))
        (∑ j, MvPolynomial.C (c j) * (frame j).1.map a) = 0) →
      c = 0 := by
  intro c hzero
  by_contra hc
  obtain ⟨tQ, p, hp, hne, α, hα, hpScale, htQBase, htQClass⟩ :=
    exists_homogeneousFrame_parameter_of_nonzero_coordinates
      a e frame hframe c hc
  let t := Spec.map (CommRingCat.ofHom b) ≫ tQ
  have htBase : r ≫ xBase = t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) := by
    calc
      r ≫ xBase = Spec.map (CommRingCat.ofHom (b.comp a)) := hrBase
      _ = Spec.map (CommRingCat.ofHom b) ≫
          Spec.map (CommRingCat.ofHom a) := by
        rw [← Spec.map_comp]
        rfl
      _ = Spec.map (CommRingCat.ofHom b) ≫
          (tQ ≫ toBase
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) :=
        congrArg (fun k => Spec.map (CommRingCat.ofHom b) ≫ k) htQBase.symm
      _ = t ≫ toBase
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) :=
        (Category.assoc _ _ _).symm
  have htClass : Spec.map (CommRingCat.ofHom b) ≫
        projectiveClassifyingMap p hp hne a =
      t ≫ homogeneousFrameToParameters d e frame hframe := by
    calc
      _ = Spec.map (CommRingCat.ofHom b) ≫
          (tQ ≫ homogeneousFrameToParameters d e frame hframe) :=
        congrArg (fun k => Spec.map (CommRingCat.ofHom b) ≫ k) htQClass.symm
      _ = _ := (Category.assoc _ _ _).symm
  have hexists : ∀ i, ∃ u : Spec (.of L) ⟶
      projectiveUniversalFamily K (Fin 4) d,
      u ≫ projectiveUniversalIncidence K (Fin 4) d =
        Limits.prod.lift (r ≫ marked i)
          (t ≫ homogeneousFrameToParameters d e frame hframe) := by
    intro i
    have hpzero : p.eval₂ (algebraMap Q L) (fun j => φ i (x j)) = 0 := by
      rw [hpScale, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
        hzero i, mul_zero]
    apply exists_projectiveUniversalFamily_point_of_mappedNormalized_evaluation_zero
      a p hp hne x he ell hell hellOne (φ i) hpzero i r marked t
      (homogeneousFrameToParameters d e frame hframe) (hmarked i)
    simpa only [hb] using htClass
  let q : Fin 16 → (Spec (.of L) ⟶
      projectiveUniversalFamily K (Fin 4) d) := fun i => (hexists i).choose
  have hq : ∀ i, q i ≫ projectiveUniversalIncidence K (Fin 4) d =
      Limits.prod.lift (r ≫ marked i)
        (t ≫ homogeneousFrameToParameters d e frame hframe) :=
    fun i => (hexists i).choose_spec
  apply hno
  refine ⟨t, q, htBase, ?_⟩
  intro i
  exact projectiveUniversalFamilyPoint_eq_finiteIncidenceParameterMap
    xBase
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    marked (homogeneousFrameToParameters d e frame hframe)
    i r t htBase (q i) (hq i)

end PfaffianDescent
