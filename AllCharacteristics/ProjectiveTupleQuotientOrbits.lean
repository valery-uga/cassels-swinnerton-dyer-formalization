import AllCharacteristics.ProjectiveTupleQuotientAction

/-!
# Actual permutation-orbit fibers of the full projective tuple quotient

Two ordered tuples can be placed in one common affine chart. The proved
orbit description of its original affine-scheme quotient then gives the
orbit description for the constructed quotient of the whole ordered power.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

omit [IsAffine S] in
/-- Two original ordered tuples lie in one common-affine-open chart. -/
theorem exists_commonAffineOpen_two_orderedProjectivePoints
    (x y : (orderedFamilyPowerOver f n).left) :
    ∃ U : (Proj 𝒜).affineOpens,
      x ∈ orderedFamilyCommonOpen f U.val n ∧ y ∈ orderedFamilyCommonOpen f U.val n := by
  classical
  let px (i : Fin n) := Over.Hom.left (orderedFamilyCoordinate f n i) x
  let py (i : Fin n) := Over.Hom.left (orderedFamilyCoordinate f n i) y
  obtain ⟨U, hU⟩ := exists_affineOpen_containing_projective_finset 𝒜
    ((Finset.univ.image px) ∪ (Finset.univ.image py))
  refine ⟨U, (mem_orderedFamilyCommonOpen_iff f U.val n x).mpr ?_,
    (mem_orderedFamilyCommonOpen_iff f U.val n y).mpr ?_⟩
  · intro i
    exact hU (px i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  · intro i
    exact hU (py i) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

/-- The fibers of the actual full projective quotient map are precisely the
orbits of the original ordered-tuple permutation maps. -/
theorem projectiveOrderedTupleQuotientMap_eq_iff_orbit
    (x y : (orderedFamilyPowerOver f n).left) :
    projectiveOrderedTupleQuotientMap 𝒜 f n x = projectiveOrderedTupleQuotientMap 𝒜 f n y ↔
      ∃ e : Equiv.Perm (Fin n), orderedFamilyRightAction f n e x = y := by
  constructor
  · intro hxy
    obtain ⟨U, hx, hy⟩ := exists_commonAffineOpen_two_orderedProjectivePoints 𝒜 f n x y
    let p : (orderedFamilyCommonOpen f U.val n).toScheme := ⟨x, hx⟩
    let q : (orderedFamilyCommonOpen f U.val n).toScheme := ⟨y, hy⟩
    have he (z : (orderedFamilyCommonOpen f U.val n).toScheme) :
        projectiveOrderedTupleQuotientMap 𝒜 f n z.val =
          commonOpenTupleQuotientGluedChart f n U (commonOpenTupleQuotientMap f U.val n U.property z) :=
      congrArg (fun m : (orderedFamilyCommonOpen f U.val n).toScheme ⟶
        projectiveOrderedTupleQuotient 𝒜 f n ↦ m z) (projectiveOrderedTupleQuotientMap_chart 𝒜 f n U)
    have hlocal : commonOpenTupleQuotientMap f U.val n U.property p =
        commonOpenTupleQuotientMap f U.val n U.property q :=
      (commonOpenTupleQuotientGluedChart f n U).isOpenEmbedding.injective
        ((he p).symm.trans (hxy.trans (he q)))
    have : IsAffine (orderedFamilyCommonOpen f U.val n).toScheme :=
      isAffineOpen_orderedFamilyCommonOpen f U.val n U.property
    obtain ⟨e, heq⟩ := (affineSchemeActionQuotientMap_eq_iff_orbit (Equiv.Perm (Fin n))
      (commonOpenRightAction f U.val n) (commonOpenRightAction_one f U.val n)
      (commonOpenRightAction_mul f U.val n)
      ((orderedFamilyCommonOpen f U.val n).ι ≫ (orderedFamilyPowerOver f n).hom)
      (commonOpenRightAction_toBase f U.val n) p q).mp hlocal
    refine ⟨e, ?_⟩
    have hact := congrArg (fun m : (orderedFamilyCommonOpen f U.val n).toScheme ⟶
        (orderedFamilyPowerOver f n).left ↦ m p) (commonOpenRightAction_toPower 𝒜 f n U.val e)
    exact hact.symm.trans (congrArg (orderedFamilyCommonOpen f U.val n).ι heq)
  · rintro ⟨e, rfl⟩
    exact (congrArg (fun m : (orderedFamilyPowerOver f n).left ⟶
      projectiveOrderedTupleQuotient 𝒜 f n ↦ m x) (projectiveOrderedTupleQuotientMap_invariant 𝒜 f n e)).symm

end AllCharacteristics
