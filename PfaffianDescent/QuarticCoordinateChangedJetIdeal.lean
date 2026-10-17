import PfaffianDescent.ProjectiveLinearCoordinateRank
import PfaffianDescent.ProjectiveCoefficientGradeBaseChange
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import PfaffianDescent.QuarticHomogeneousJets
import PfaffianDescent.QuarticExceptionalProjectiveLength
import AllCharacteristics.ProjectiveBaseChangeFiniteRank

/-!
# Coordinate changes of the Section 4 quadric--cubic intersection

This records the homogeneous ideal obtained by first extending coefficients
and then applying an invertible linear coordinate substitution.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

theorem coordinateChanged_jetQuadricCubicIntersectionIdeal_toIdeal
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) :
    (jetQuadricCubicIntersectionIdeal
      (fun i => linearSubstitution M (map (algebraMap k K) (Q i)))
      (fun i => linearSubstitution_homogeneous M ((hQ i).map (algebraMap k K)))
      (linearSubstitution M (map (algebraMap k K) F))
      (linearSubstitution_homogeneous M (hF.map (algebraMap k K)))).toIdeal =
      (jetQuadricCubicIntersectionIdeal
        (fun i => map (algebraMap k K) (Q i))
        (fun i => (hQ i).map (algebraMap k K))
        (map (algebraMap k K) F) (hF.map (algebraMap k K))).toIdeal.map
          (linearSubstitutionEquiv M hM).toRingHom := by
  change Ideal.span (Set.range (fun i => linearSubstitution M (map (algebraMap k K) (Q i)))) ⊔
      Ideal.span {linearSubstitution M (map (algebraMap k K) F)} =
    (Ideal.span (Set.range (fun i => map (algebraMap k K) (Q i))) ⊔
      Ideal.span {map (algebraMap k K) F}).map (linearSubstitutionEquiv M hM).toRingHom
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  have hrange : (⇑(linearSubstitutionEquiv M hM).toRingHom ''
      Set.range (fun i => map (algebraMap k K) (Q i))) =
      Set.range (fun i => linearSubstitution M (map (algebraMap k K) (Q i))) := by
    ext p
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨map (algebraMap k K) (Q i), ⟨i, rfl⟩, rfl⟩
  have hsingle : (⇑(linearSubstitutionEquiv M hM).toRingHom ''
      ({map (algebraMap k K) F} : Set (MvPolynomial (Fin 4) K))) =
      {linearSubstitution M (map (algebraMap k K) F)} := by
    ext p
    constructor
    · rintro ⟨_, hp, rfl⟩
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact Set.mem_singleton _
    · rintro rfl
      exact ⟨map (algebraMap k K) F, Set.mem_singleton _, rfl⟩
  rw [hrange, hsingle]

/-- Extending coefficients commutes with forming the homogeneous
three-quadric--cubic intersection ideal. -/
theorem coefficientChanged_jetQuadricCubicIntersectionIdeal_toIdeal
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) :
    (jetQuadricCubicIntersectionIdeal
      (fun i => map (algebraMap k K) (Q i))
      (fun i => (hQ i).map (algebraMap k K))
      (map (algebraMap k K) F) (hF.map (algebraMap k K))).toIdeal =
      (jetQuadricCubicIntersectionIdeal Q hQ F hF).toIdeal.map
        (map (algebraMap k K)) := by
  change Ideal.span (Set.range (fun i => map (algebraMap k K) (Q i))) ⊔
      Ideal.span {map (algebraMap k K) F} =
    (Ideal.span (Set.range Q) ⊔ Ideal.span {F}).map (map (algebraMap k K))
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  have hrange : (map (algebraMap k K) '' Set.range Q) =
      Set.range (fun i => map (algebraMap k K) (Q i)) := by
    ext p
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Q i, ⟨i, rfl⟩, rfl⟩
  have hsingle : (map (algebraMap k K) '' ({F} : Set (MvPolynomial (Fin 4) k))) =
      {map (algebraMap k K) F} := by
    ext p
    constructor
    · rintro ⟨_, hp, rfl⟩
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact Set.mem_singleton _
    · rintro rfl
      exact ⟨F, Set.mem_singleton _, rfl⟩
  rw [hrange, hsingle]

/-- Contracting the coefficient extension of the quadric--cubic ideal gives
back the original ground-field ideal. -/
theorem coefficientChanged_jetQuadricCubicIntersectionIdeal_comap_toIdeal
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) :
    Ideal.comap (MvPolynomial.map (algebraMap k K))
      (jetQuadricCubicIntersectionIdeal
        (fun i => map (algebraMap k K) (Q i))
        (fun i => (hQ i).map (algebraMap k K))
        (map (algebraMap k K) F) (hF.map (algebraMap k K))).toIdeal =
      (jetQuadricCubicIntersectionIdeal Q hQ F hF).toIdeal := by
  rw [coefficientChanged_jetQuadricCubicIntersectionIdeal_toIdeal]
  exact mvPolynomial_comap_map_coefficientExtension _

/-- The coefficient-changed exceptional quadric--cubic intersection has
homogeneous coordinate dimension nine from degree three onward. -/
theorem coefficientChanged_jetQuadricCubicIntersection_exceptional_grade_finrank [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (hQideal : Ideal.span (Set.range (fun i =>
      linearSubstitution M (map (algebraMap k K) (Q i)))) =
        RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom)
    (hnonzero : exceptionalTwistedCubicParam a b c d e
      (linearSubstitution M (map (algebraMap k K) F)) ≠ 0)
    (n : ℕ) (hn : 3 ≤ n) :
    Module.finrank K (grading (jetQuadricCubicIntersectionIdeal
      (fun i => map (algebraMap k K) (Q i))
      (fun i => (hQ i).map (algebraMap k K))
      (map (algebraMap k K) F) (hF.map (algebraMap k K))) n) = 9 := by
  let I := jetQuadricCubicIntersectionIdeal
    (fun i => map (algebraMap k K) (Q i))
    (fun i => (hQ i).map (algebraMap k K))
    (map (algebraMap k K) F) (hF.map (algebraMap k K))
  let J := jetQuadricCubicIntersectionIdeal
    (fun i => linearSubstitution M (map (algebraMap k K) (Q i)))
    (fun i => linearSubstitution_homogeneous M ((hQ i).map (algebraMap k K)))
    (linearSubstitution M (map (algebraMap k K) F))
    (linearSubstitution_homogeneous M (hF.map (algebraMap k K)))
  have hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom := by
    simpa only [I, J] using
      coordinateChanged_jetQuadricCubicIntersectionIdeal_toIdeal M hM Q hQ F hF
  have hJexceptional : J = exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f
      (linearSubstitution M (map (algebraMap k K) F))
      (linearSubstitution_homogeneous M (hF.map (algebraMap k K))) := by
    simpa only [J] using
      jetQuadricCubicIntersectionIdeal_eq_exceptional_of_ideal_eq_param_ker
        a b c d e f ha hb hc hd he hdelta
        (fun i => linearSubstitution M (map (algebraMap k K) (Q i)))
        (fun i => linearSubstitution_homogeneous M ((hQ i).map (algebraMap k K)))
        hQideal (linearSubstitution M (map (algebraMap k K) F))
        (linearSubstitution_homogeneous M (hF.map (algebraMap k K)))
  calc
    Module.finrank K (grading I n) = Module.finrank K (grading J n) :=
      linearCoordinateChange_grade_finrank M hM I J hIJ n
    _ = 9 := by
      rw [hJexceptional]
      exact exceptionalTwistedCubicCubicIntersection_grade_finrank
        a b c d e f ha hb hc hd he hdelta
        (linearSubstitution M (map (algebraMap k K) F))
        (linearSubstitution_homogeneous M (hF.map (algebraMap k K))) hnonzero n hn

/-- After coefficient extension, the untransformed quadric--cubic
intersection has rank nine whenever an invertible coordinate change identifies
its three-quadric ideal with the exceptional twisted-cubic kernel. -/
theorem coefficientChanged_jetQuadricCubicIntersection_exceptional_finiteSchemeRank [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (hQideal : Ideal.span (Set.range (fun i =>
      linearSubstitution M (map (algebraMap k K) (Q i)))) =
        RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom)
    (hnonzero : exceptionalTwistedCubicParam a b c d e
      (linearSubstitution M (map (algebraMap k K) F)) ≠ 0) :
    ∃ hfinite : IsFinite (toBase (jetQuadricCubicIntersectionIdeal
      (fun i => map (algebraMap k K) (Q i))
      (fun i => (hQ i).map (algebraMap k K))
      (map (algebraMap k K) F) (hF.map (algebraMap k K)))),
      @AllCharacteristics.finiteSchemeRank K _ _ (toBase
        (jetQuadricCubicIntersectionIdeal
          (fun i => map (algebraMap k K) (Q i))
          (fun i => (hQ i).map (algebraMap k K))
          (map (algebraMap k K) F) (hF.map (algebraMap k K)))) hfinite = 9 := by
  let I := jetQuadricCubicIntersectionIdeal
    (fun i => map (algebraMap k K) (Q i))
    (fun i => (hQ i).map (algebraMap k K))
    (map (algebraMap k K) F) (hF.map (algebraMap k K))
  let J := jetQuadricCubicIntersectionIdeal
    (fun i => linearSubstitution M (map (algebraMap k K) (Q i)))
    (fun i => linearSubstitution_homogeneous M ((hQ i).map (algebraMap k K)))
    (linearSubstitution M (map (algebraMap k K) F))
    (linearSubstitution_homogeneous M (hF.map (algebraMap k K)))
  have hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom := by
    simpa only [I, J] using
      coordinateChanged_jetQuadricCubicIntersectionIdeal_toIdeal M hM Q hQ F hF
  have hJexceptional : J = exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f
      (linearSubstitution M (map (algebraMap k K) F))
      (linearSubstitution_homogeneous M (hF.map (algebraMap k K))) := by
    simpa only [J] using
      jetQuadricCubicIntersectionIdeal_eq_exceptional_of_ideal_eq_param_ker
        a b c d e f ha hb hc hd he hdelta
        (fun i => linearSubstitution M (map (algebraMap k K) (Q i)))
        (fun i => linearSubstitution_homogeneous M ((hQ i).map (algebraMap k K)))
        hQideal (linearSubstitution M (map (algebraMap k K) F))
        (linearSubstitution_homogeneous M (hF.map (algebraMap k K)))
  have hJgrade : ∀ n, 3 ≤ n → Module.finrank K (grading J n) = 9 := by
    intro n hn
    rw [hJexceptional]
    exact exceptionalTwistedCubicCubicIntersection_grade_finrank
      a b c d e f ha hb hc hd he hdelta
      (linearSubstitution M (map (algebraMap k K) F))
      (linearSubstitution_homogeneous M (hF.map (algebraMap k K))) hnonzero n hn
  simpa only [I] using
    (projective_finiteSchemeRank_of_linearCoordinateChange_eventual_hilbert
      M hM I J hIJ 3 9 hJgrade)

/-- Finiteness of the exceptional quadric--cubic intersection descends from
its coefficient extension. -/
theorem ground_jetQuadricCubicIntersection_exceptional_isFinite [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (hQideal : Ideal.span (Set.range (fun i =>
      linearSubstitution M (map (algebraMap k K) (Q i)))) =
        RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom)
    (hnonzero : exceptionalTwistedCubicParam a b c d e
      (linearSubstitution M (map (algebraMap k K) F)) ≠ 0) :
    IsFinite (toBase (jetQuadricCubicIntersectionIdeal Q hQ F hF)) := by
  let I := jetQuadricCubicIntersectionIdeal Q hQ F hF
  let J := jetQuadricCubicIntersectionIdeal
    (fun i => map (algebraMap k K) (Q i))
    (fun i => (hQ i).map (algebraMap k K))
    (map (algebraMap k K) F) (hF.map (algebraMap k K))
  have hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal := by
    simpa only [I, J] using
      (coefficientChanged_jetQuadricCubicIntersectionIdeal_toIdeal Q hQ F hF).symm
  have hJ : ∀ n, 3 ≤ n → Module.finrank K (grading J n) ≤ 9 := by
    intro n hn
    simpa only [J] using
      (coefficientChanged_jetQuadricCubicIntersection_exceptional_grade_finrank
        M hM Q hQ F hF a b c d e f ha hb hc hd he hdelta hQideal hnonzero n hn).le
  simpa only [I] using
    (projective_finite_of_coefficientExtension_hilbert_bound I J hIJ 3 9 hJ)

/-- Once the ground quadric--cubic intersection is known finite, its
exceptional coordinate description forces its rank to be nine. -/
theorem ground_jetQuadricCubicIntersection_exceptional_finiteSchemeRank [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (hQideal : Ideal.span (Set.range (fun i =>
      linearSubstitution M (map (algebraMap k K) (Q i)))) =
        RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom)
    (hnonzero : exceptionalTwistedCubicParam a b c d e
      (linearSubstitution M (map (algebraMap k K) F)) ≠ 0)
    [IsFinite (toBase (jetQuadricCubicIntersectionIdeal Q hQ F hF))] :
    AllCharacteristics.finiteSchemeRank
      (toBase (jetQuadricCubicIntersectionIdeal Q hQ F hF)) = 9 := by
  obtain ⟨hfinite, hrank⟩ :=
    coefficientChanged_jetQuadricCubicIntersection_exceptional_finiteSchemeRank
      M hM Q hQ F hF a b c d e f ha hb hc hd he hdelta hQideal hnonzero
  letI : IsFinite (toBase (jetQuadricCubicIntersectionIdeal
      (fun i => map (algebraMap k K) (Q i))
      (fun i => (hQ i).map (algebraMap k K))
      (map (algebraMap k K) F) (hF.map (algebraMap k K)))) := hfinite
  exact (AllCharacteristics.HomogeneousProjective.projective_finiteSchemeRank_baseChange
    (jetQuadricCubicIntersectionIdeal Q hQ F hF)
    (jetQuadricCubicIntersectionIdeal
      (fun i => map (algebraMap k K) (Q i))
      (fun i => (hQ i).map (algebraMap k K))
      (map (algebraMap k K) F) (hF.map (algebraMap k K)))
    (coefficientChanged_jetQuadricCubicIntersectionIdeal_toIdeal Q hQ F hF).symm).trans hrank

/-- The exceptional coordinate calculation and an embedded rank-eight jet
produce a rational cubic section as soon as the ground quadric--cubic
intersection is finite. -/
theorem cubic_section_of_ground_exceptional_jet_intersection [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (hQideal : Ideal.span (Set.range (fun i =>
      linearSubstitution M (map (algebraMap k K) (Q i)))) =
        RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom)
    (hnonzero : exceptionalTwistedCubicParam a b c d e
      (linearSubstitution M (map (algebraMap k K) F)) ≠ 0)
    {Z : Scheme.{u}} (j : Z ⟶ scheme (jetQuadricCubicIntersectionIdeal Q hQ F hF))
    [IsClosedImmersion j]
    [IsFinite (j ≫ jetQuadricCubicIntersectionToHypersurface Q hQ F hF ≫
      hypersurfaceToBase F hF)]
    (hjet : AllCharacteristics.finiteSchemeRank
      (j ≫ jetQuadricCubicIntersectionToHypersurface Q hQ F hF ≫
        hypersurfaceToBase F hF) = 8) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  letI : IsFinite (toBase (jetQuadricCubicIntersectionIdeal Q hQ F hF)) :=
    ground_jetQuadricCubicIntersection_exceptional_isFinite
      M hM Q hQ F hF a b c d e f ha hb hc hd he hdelta hQideal hnonzero
  let ι := jetQuadricCubicIntersectionToHypersurface Q hQ F hF
  letI : IsFinite (ι ≫ hypersurfaceToBase F hF) := by
    rw [jetQuadricCubicIntersectionToHypersurface_toBase]
    infer_instance
  have hX : AllCharacteristics.finiteSchemeRank (ι ≫ hypersurfaceToBase F hF) = 9 := by
    have hground := ground_jetQuadricCubicIntersection_exceptional_finiteSchemeRank
      M hM Q hQ F hF a b c d e f ha hb hc hd he hdelta hQideal hnonzero
    simpa only [ι, jetQuadricCubicIntersectionToHypersurface_toBase] using hground
  exact cubic_section_of_rank_nine_exceptional_intersection F hF ι j hX (by
    simpa only [ι] using hjet)

end QuarticNet
end PfaffianDescent
