import PfaffianDescent.CubicLineFiniteSubscheme
import PfaffianDescent.CorayAiNoSectionRankThreeCutField
import PfaffianDescent.CorayEntireModelIncidenceCycle
import AllCharacteristics.ProjectiveRingPoints

/-! SOURCE ONLY. Explicit original-K normalized-direction cubic cut. The
actual AdjoinRoot algebra, root-coordinate vector and literal normalized
projective map are retained. No chart-j/q0/badimage avoidance is asserted. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual original-K normalized endpoint on the cubic would be a section. -/
private theorem originalCubic_noSection_normalizedEndpoint_nonzero001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = p)
    (a : Fin 4 → K) (i : Fin 4) (hai : a i = 1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) : c.eval a ≠ 0 := by
  intro hzero
  have hpx : p.eval₂ (RingHom.id K) a = 0 := by
    rw [← hc, Cubic.eval_toMvPolynomial]
    exact hzero
  obtain ⟨s, hs⟩ := hypersurface_point_of_unit_coordinates
    (RingHom.id K) p hp a i (hai.symm ▸ isUnit_one) hpx
  exact hno ⟨s, by simpa using hs⟩

/-- A SAME actual embedded original-K rank-three algebra becomes a field;
its actual closed image has full original degree three and residue-map iso. -/
private theorem originalAffineRankThreeClosedMap_noSection_fullDegreePoint001
    {B : Type u} [CommRing B] [Algebra K B] [Module.Finite K B]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (r : Spec (.of B) ⟶ hypersurface p hp) [IsClosedImmersion r]
    (hbase : r ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (hrank : Module.finrank K B = 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ hField : IsField B,
      letI : Field B := hField.toField
      ∃ A : closedPoints (hypersurface p hp),
        A.1 = r (IsLocalRing.closedPoint B) ∧
        IsIso (r.residueFieldMap (IsLocalRing.closedPoint B)) ∧
        (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
  have hField := cubic_noSection_rankThree_affineClosedCut_isField001
    p hp r hbase hrank hno
  refine ⟨hField, ?_⟩
  letI : Field B := hField.toField
  let b : Spec (.of B) := IsLocalRing.closedPoint B
  let A : closedPoints (hypersurface p hp) := ⟨r b, by
    change IsClosed ({r b} : Set (hypersurface p hp))
    rw [← Set.image_singleton]
    exact r.isClosedMap _ isClosed_singleton⟩
  letI : IsIso (r.residueFieldMap b) :=
    isIso_residueFieldMap_of_surjectiveOnStalks r b
  have hDegree : (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
    have h := residueDegree_comp_of_residueFieldMap_isIso r (hypersurfaceToBase p hp) b
    rw [hbase] at h
    exact h.symm.trans ((modelFieldSpectrum_original_residueDegree_eq_finrank
      (K := K) (M := B)).trans hrank)
  exact ⟨A, rfl, inferInstance, hDegree⟩

/-- The literal normalized-direction cut retains B=AdjoinRoot of the actual
restricted original cubic, x=root*a+b and its actual normalized chart map.
No-section derives the leading endpoint nonzero, fieldness and full degree3.
This constructs a selected original line cut, without any avoidance claim. -/
theorem originalNormalizedDirection_noSection_explicit_rankThree_cut_and_fullDegreePoint001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = p)
    (a b : Fin 4 → K) (i j : Fin 4)
    (hai : a i = 1) (hbi : b i = 0) (hbj : b j = 1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    let F := cubicLinePolynomial c a b
    let B := AdjoinRoot F
    let x : Fin 4 → B :=
      AdjoinRoot.root F • (fun k => algebraMap K B (a k)) +
        (fun k => algebraMap K B (b k))
    let ell : MvPolynomial (Fin 4) K := X j - C (a j) * X i
    let I := equationIdeal p hp
    ∃ hBFinite : Module.Finite K B,
      letI := hBFinite
      ∃ (hell : ell.IsHomogeneous 1)
        (hxell : ell.eval₂ (algebraMap K B) x = 1)
        (heI : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K B) x = 0),
        let r : Spec (.of B) ⟶ hypersurface p hp :=
          linearNormalizedPoint I x ell hell hxell heI
        IsClosedImmersion r ∧
        r ≫ hypersurfaceToBase p hp =
          Spec.map (CommRingCat.ofHom (algebraMap K B)) ∧
        Module.finrank K B = 3 ∧
        (∀ k : Fin 4, linearNormalizedPointChartMap I x ell hxell heI
          (linearChartCoordinate I (Ideal.Quotient.mk I.toIdeal ell)
            (polynomial_class_mem_grading I ell hell) k) = x k) ∧
        ∃ hFinite : IsFinite (r ≫ hypersurfaceToBase p hp),
          letI := hFinite
          finiteSchemeRank (r ≫ hypersurfaceToBase p hp) = 3 ∧
          ∃ hField : IsField B,
            letI : Field B := hField.toField
            ∃ A : closedPoints (hypersurface p hp),
              A.1 = r (IsLocalRing.closedPoint B) ∧
              IsIso (r.residueFieldMap (IsLocalRing.closedPoint B)) ∧
              (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
  classical
  let F := cubicLinePolynomial c a b
  let B := AdjoinRoot F
  let x : Fin 4 → B :=
    AdjoinRoot.root F • (fun k => algebraMap K B (a k)) +
      (fun k => algebraMap K B (b k))
  let ell : MvPolynomial (Fin 4) K := X j - C (a j) * X i
  let I := equationIdeal p hp
  have ha : c.eval a ≠ 0 :=
    originalCubic_noSection_normalizedEndpoint_nonzero001 p hp c hc a i hai hno
  have hDegreeF : F.natDegree = 3 := cubicLinePolynomial_natDegree c a b ha
  have hF : F ≠ 0 := by
    intro hzero
    simp [hzero] at hDegreeF
  let pb := AdjoinRoot.powerBasis hF
  letI hBFinite : Module.Finite K B := Module.Finite.of_basis pb.basis
  have hRankB : Module.finrank K B = 3 := pb.finrank.trans hDegreeF
  have hxi : x i = AdjoinRoot.root F := by simp [x, hai, hbi]
  have hxj : x j = AdjoinRoot.root F * algebraMap K B (a j) + 1 := by
    simp [x, hbj]
  have hcx : (c.map (algebraMap K B)).eval x = 0 := by
    rw [← cubicLinePolynomial_eval₂ (algebraMap K B) c a b (AdjoinRoot.root F)]
    exact AdjoinRoot.eval₂_root F
  have hpx : p.eval₂ (algebraMap K B) x = 0 := by
    rw [← hc, Cubic.eval_toMvPolynomial]
    exact hcx
  have heI : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K B) x = 0 := by
    have hle : I.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K B) x) := by
      apply Ideal.span_le.mpr
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      exact hpx
    exact fun f hf => hle hf
  have hell : ell.IsHomogeneous 1 := by
    exact (isHomogeneous_X K j).sub
      (by simpa [ell] using isHomogeneous_C_mul_X (a j) i)
  have hxell : ell.eval₂ (algebraMap K B) x = 1 := by
    rw [show ell.eval₂ (algebraMap K B) x =
      x j - algebraMap K B (a j) * x i by simp [ell]]
    rw [hxj, hxi]
    ring
  let r : Spec (.of B) ⟶ hypersurface p hp :=
    linearNormalizedPoint I x ell hell hxell heI
  have hClosed : IsClosedImmersion r :=
    linearNormalizedPoint_isClosedImmersion I x ell hell hxell heI
      (eval₂_line_coordinate_surjective F i x hxi)
  letI : IsClosedImmersion r := hClosed
  have hbase : r ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) :=
    linearNormalizedPoint_toBase I x ell hell hxell heI
  have hFinite : IsFinite (r ≫ hypersurfaceToBase p hp) := by
    rw [hbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite (r ≫ hypersurfaceToBase p hp) := hFinite
  have hRankScheme : finiteSchemeRank (r ≫ hypersurfaceToBase p hp) = 3 := by
    rw [finiteSchemeRank_eq_finrank, hbase, Scheme.Hom.finrank_SpecMap_algebraMap]
    exact (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := B)) _).trans hRankB
  obtain ⟨hField, hPoint⟩ := originalAffineRankThreeClosedMap_noSection_fullDegreePoint001
    p hp r hbase hRankB hno
  refine ⟨hBFinite, hell, hxell, heI, hClosed, hbase, hRankB, ?_, hFinite,
    hRankScheme, hField, hPoint⟩
  intro k
  exact linearNormalizedPointChartMap_coordinate I x ell hell hxell heI k

end PfaffianDescent.Coray
