import PfaffianDescent.VoisinDetectedProjectiveIncidence
import PfaffianDescent.VoisinResidueProjectiveCoordinates
import AllCharacteristics.FiniteFieldPointResidueEmbedding
import AllCharacteristics.UniversalProjectiveFiniteIncidence

/-!
# A detecting residue point avoids the quadratic-frame bad locus

This file connects residue-field coordinates of eight marked projective
points to the universal finite-incidence bad locus.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If the eight marked points at a scheme point have normalized coordinates
over its residue field which detect the fixed quadratic frame, then that point
is outside the corresponding universal finite-incidence bad locus. -/
theorem residuePoint_not_mem_quadraticEightFrameBadLocus_of_detecting_coordinates
    {K : Type u} [Field K]
    {X : Scheme.{u}}
    (xBase : X ⟶ Spec (.of K))
    (marked : Fin 8 →
      (X ⟶ Proj (homogeneousSubmodule (Fin 4) K)))
    (z : X) :
    let Q := X.residueField z
    letI : Algebra K Q := pointAlgebra xBase z
    ∀ (j : Fin 8 → Fin 4) (y : Fin 8 → Fin 4 → Q),
      (∀ i, y i (j i) = 1) →
      (∀ i, ∃
        (he : ∀ p ∈ (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) K)).toIdeal,
            p.eval₂ (algebraMap K Q) (y i) = 0)
        (hX : (MvPolynomial.X (j i)).eval₂ (algebraMap K Q) (y i) = 1),
        linearNormalizedPoint
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
            (y i) (MvPolynomial.X (j i)) (isHomogeneous_X K (j i)) hX he ≫
          quotientProjMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) =
          X.fromSpecResidueField z ≫ marked i) →
      (∀ c : Fin 8 → Q,
        (∀ i, eval (y i)
          (homogeneousFrameMap 2 (quadraticEightFrame Q) c).1 = 0) →
        c = 0) →
      z ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
        xBase
        (toBase (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 8) K)))
        marked
        (homogeneousFrameToParameters 2
          ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
          (quadraticEightFrame K)
          (quadraticEightFrame_linearIndependent K)) := by
  dsimp only
  intro j y hyj hmarked hdetect hzbad
  letI : Algebra K (X.residueField z) := pointAlgebra xBase z
  let tBase := toBase
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K))
  let frameMap := homogeneousFrameToParameters 2
    ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
    (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K)
  obtain ⟨w, hwfst, hwinc⟩ :=
    exists_parameter_of_mem_projectiveUniversalFiniteIncidenceBadLocus
      K (Fin 4) 2 xBase tBase marked frameMap hzbad
  obtain ⟨L, hL, r, u, hrange, hu⟩ :=
    exists_common_fieldPoint_of_mem_all_parameterMap_range
      K (Fin 4) 2 xBase tBase marked frameMap w hwinc
  letI : Field L := hL
  let cL : Spec (.of L) := IsLocalRing.closedPoint L
  have hrcL : r cL = w := by
    have hmem : r cL ∈ Set.range r := ⟨cL, rfl⟩
    rw [hrange] at hmem
    simpa only [Set.mem_singleton_iff] using hmem
  let rX : Spec (.of L) ⟶ X := r ≫ pullback.fst xBase tBase
  let t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin 8) :=
    r ≫ pullback.snd xBase tBase
  have hrXz : rX cL = z := by
    change pullback.fst xBase tBase (r cL) = z
    rw [hrcL, hwfst]
  let f : K →+* L := (Spec.preimage (rX ≫ xBase)).hom
  letI : Algebra K L := f.toAlgebra
  have hf : rX ≫ xBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    change rX ≫ xBase = Spec.map (CommRingCat.ofHom f)
    exact (Spec.map_preimage (rX ≫ xBase)).symm
  let b : X.residueField z →ₐ[K] L :=
    fieldPointResidueAlgHomAt xBase rX hf z hrXz
  have hbSpec : Spec.map (CommRingCat.ofHom b.toRingHom) ≫
      X.fromSpecResidueField z = rX :=
    fieldPointResidueAlgHomAt_spec xBase rX hf z hrXz
  let yL : Fin 8 → Fin 4 → L := fun i k => b (y i k)
  have hyjL : ∀ i, yL i (j i) = 1 := by
    intro i
    simp [yL, hyj i]
  have hdetectL : ∀ c : Fin 8 → L,
      (∀ i, eval (yL i)
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0 :=
    quadraticEightFrame_detection_persists b.toRingHom y hdetect
  have ht : t ≫ tBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    calc
      t ≫ tBase = rX ≫ xBase := by
        dsimp only [t, rX]
        rw [Category.assoc, Category.assoc, pullback.condition]
      _ = _ := hf
  have huBase : ∀ i, u i ≫ projectiveUniversalToBase K (Fin 4) 2 =
      t ≫ frameMap := by
    intro i
    calc
      u i ≫ projectiveUniversalToBase K (Fin 4) 2 =
          u i ≫ projectiveUniversalIncidence K (Fin 4) 2 ≫
            Limits.prod.snd := by
        rw [projectiveUniversalIncidence_snd]
      _ = r ≫ projectiveUniversalFiniteIncidenceParameterMap
          K (Fin 4) 2 xBase tBase marked frameMap i ≫
            Limits.prod.snd := by
        simpa only [Category.assoc] using
          congrArg (fun g => g ≫ Limits.prod.snd) (hu i)
      _ = t ≫ frameMap := by
        dsimp only [t]
        exact congrArg (fun g => r ≫ g)
          (projectiveUniversalFiniteIncidenceParameterMap_snd
            K (Fin 4) 2 xBase tBase marked frameMap i)
  have huAmbient : ∀ i,
      u i ≫ projectiveUniversalToAmbient K (Fin 4) 2 =
        let I0 : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) K) := ⊥
        let heL : ∀ p ∈ I0.toIdeal,
            p.eval₂ (algebraMap K L) (yL i) = 0 := by
          intro p hp
          rw [Ideal.mem_bot.mp hp]
          simp
        let hXL : (MvPolynomial.X (j i)).eval₂
            (algebraMap K L) (yL i) = 1 := by
          simpa only [MvPolynomial.eval₂_X] using hyjL i
        linearNormalizedPoint I0 (yL i) (MvPolynomial.X (j i))
            (isHomogeneous_X K (j i)) hXL heL ≫ quotientProjMap I0 := by
    intro i
    obtain ⟨heQ, hXQ, hmarkedQ⟩ := hmarked i
    let I0 : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
    let heL : ∀ p ∈ I0.toIdeal,
        p.eval₂ (algebraMap K L) (yL i) = 0 := by
      intro p hp
      rw [Ideal.mem_bot.mp hp]
      simp
    let hXL : (MvPolynomial.X (j i)).eval₂ (algebraMap K L) (yL i) = 1 := by
      simpa only [MvPolynomial.eval₂_X] using hyjL i
    have hnat : linearNormalizedPoint I0 (yL i) (MvPolynomial.X (j i))
          (isHomogeneous_X K (j i)) hXL heL =
        Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          linearNormalizedPoint I0 (y i) (MvPolynomial.X (j i))
            (isHomogeneous_X K (j i)) hXQ heQ := by
      exact linearNormalizedPointAt_naturality I0 (y i) heQ b (yL i)
        (fun _ => rfl) heL
        (Ideal.Quotient.mk I0.toIdeal (MvPolynomial.X (j i)))
        (polynomial_class_mem_grading I0 (MvPolynomial.X (j i))
          (isHomogeneous_X K (j i))) hXQ hXL
    calc
      u i ≫ projectiveUniversalToAmbient K (Fin 4) 2 =
          r ≫ projectiveUniversalFiniteIncidenceParameterMap
            K (Fin 4) 2 xBase tBase marked frameMap i ≫
              Limits.prod.fst := by
        rw [← projectiveUniversalIncidence_fst]
        simpa only [Category.assoc] using
          congrArg (fun g => g ≫ Limits.prod.fst) (hu i)
      _ = rX ≫ marked i := by
        dsimp only [rX]
        exact congrArg (fun g => r ≫ g)
          (projectiveUniversalFiniteIncidenceParameterMap_fst
            K (Fin 4) 2 xBase tBase marked frameMap i)
      _ = Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          (X.fromSpecResidueField z ≫ marked i) := by
        rw [← Category.assoc, hbSpec]
      _ = Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          ((linearNormalizedPoint I0 (y i) (MvPolynomial.X (j i))
              (isHomogeneous_X K (j i)) hXQ heQ) ≫
            quotientProjMap I0) := by rw [hmarkedQ]
      _ = (Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          linearNormalizedPoint I0 (y i) (MvPolynomial.X (j i))
            (isHomogeneous_X K (j i)) hXQ heQ) ≫
            quotientProjMap I0 := (Category.assoc _ _ _).symm
      _ = linearNormalizedPoint I0 (yL i) (MvPolynomial.X (j i))
            (isHomogeneous_X K (j i)) hXL heL ≫
            quotientProjMap I0 := by rw [← hnat]
  have hdetectMapped : ∀ c : Fin 8 → L,
      (∀ i, eval (yL i)
        (∑ k, C (c k) *
          (quadraticEightFrame K k).1.map (algebraMap K L)) = 0) →
      c = 0 := by
    intro c hc
    apply hdetectL c
    intro i
    simpa only [homogeneousFrameMap, Fintype.linearCombination_apply,
      Submodule.coe_sum, Submodule.coe_smul,
      MvPolynomial.smul_eq_C_mul, quadraticEightFrame_map] using hc i
  exact universalFamily_lifts_impossible_of_frameDetection
    ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
    (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K)
    t ht yL j hyjL u huBase huAmbient hdetectMapped

end PfaffianDescent
