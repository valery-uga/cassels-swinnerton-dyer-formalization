import PfaffianDescent.VoisinCubicCoordinateNormalization
import PfaffianDescent.VoisinCoordinateOnePDeriv
import PfaffianDescent.NormalizedProjectiveClosedPoint
import PfaffianDescent.VoisinUniversalFourLineChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Descent of a transverse generic line

A separable line section after any field extension proves that the universal
line discriminant is nonzero over the ground field.  Polynomial avoidance over
an infinite field then produces a transverse line over that field itself.
-/

namespace PfaffianDescent

open MvPolynomial Polynomial AlgebraicGeometry
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev GenericCubicLineParameters := Fin 2 × Fin 4

noncomputable def genericCubicLineBase
    (K : Type u) [Field K] : Fin 4 → MvPolynomial GenericCubicLineParameters K :=
  fun i => X (0, i)

noncomputable def genericCubicLineDirection
    (K : Type u) [Field K] : Fin 4 → MvPolynomial GenericCubicLineParameters K :=
  fun i => X (1, i)

theorem genericCubicLineBase_eval₂
    {K : Type u} {L : Type v} [Field K] [Field L]
    (f : K →+* L) (a b : Fin 4 → L) :
    (fun i => MvPolynomial.eval₂ f
      (fun q : GenericCubicLineParameters => if q.1 = 0 then a q.2 else b q.2)
      (genericCubicLineBase K i)) = a := by
  funext i
  simp [genericCubicLineBase]

theorem genericCubicLineDirection_eval₂
    {K : Type u} {L : Type v} [Field K] [Field L]
    (f : K →+* L) (a b : Fin 4 → L) :
    (fun i => MvPolynomial.eval₂ f
      (fun q : GenericCubicLineParameters => if q.1 = 0 then a q.2 else b q.2)
      (genericCubicLineDirection K i)) = b := by
  funext i
  simp [genericCubicLineDirection]

theorem genericCubicLine_baseEvaluation_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4)
    (hc : ∃ a : Fin 4 → K, c.eval a ≠ 0) :
    (c.map MvPolynomial.C).eval (genericCubicLineBase K) ≠ 0 := by
  obtain ⟨a, ha⟩ := hc
  let x : GenericCubicLineParameters → K :=
    fun q => if q.1 = 0 then a q.2 else 0
  intro hzero
  have h := congrArg (MvPolynomial.eval x) hzero
  have heval := parameterizedCubic_baseEvaluation_eval c
    (genericCubicLineBase K) x
  rw [map_zero] at h
  rw [heval] at h
  apply ha
  simpa [x, genericCubicLineBase] using h

/-- A transverse line over an extension field certifies that the universal
ground-field line discriminant is a nonzero parameter polynomial. -/
theorem genericCubicLine_discr_ne_zero_of_extension_witness
    {K : Type u} {L : Type v} [Field K] [Field L] [CharZero K] [CharZero L]
    (f : K →+* L) (c : Cubic K 4)
    (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0)
    (a b : Fin 4 → L) (ha : (c.map f).eval a ≠ 0)
    (hsep : (AllCharacteristics.cubicLinePolynomial (c.map f) a b).Separable) :
    (parameterizedCubicLinePolynomial c
      (genericCubicLineBase K) (genericCubicLineDirection K)).discr ≠ 0 := by
  let P := parameterizedCubicLinePolynomial c
    (genericCubicLineBase K) (genericCubicLineDirection K)
  have hbase : (c.map MvPolynomial.C).eval (genericCubicLineBase K) ≠ 0 :=
    genericCubicLine_baseEvaluation_ne_zero c hc
  have hPdegree : P.degree = 3 := by
    apply (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr
    exact AllCharacteristics.cubicLinePolynomial_natDegree
      (c.map MvPolynomial.C) _ _ hbase
  let x : GenericCubicLineParameters → L :=
    fun q => if q.1 = 0 then a q.2 else b q.2
  let φ := MvPolynomial.eval₂Hom f x
  have hmap : P.map φ =
      AllCharacteristics.cubicLinePolynomial (c.map f) a b := by
    rw [show P = parameterizedCubicLinePolynomial c
      (genericCubicLineBase K) (genericCubicLineDirection K) by rfl,
      parameterizedCubicLinePolynomial_map_eval₂]
    rw [genericCubicLineBase_eval₂, genericCubicLineDirection_eval₂]
  have hmapDegree : (P.map φ).degree = 3 := by
    rw [hmap]
    apply (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr
    exact AllCharacteristics.cubicLinePolynomial_natDegree (c.map f) a b ha
  have hmapDisc : (P.map φ).discr ≠ 0 := by
    rw [hmap]
    exact cubic_discr_ne_zero_of_separable _
      (by rw [← hmap]; exact hmapDegree) hsep
  exact cubic_discr_ne_zero_of_specialization φ P hPdegree hmapDegree hmapDisc

/-- A transverse line found over an extension descends to the existence of a
transverse line over the original infinite characteristic-zero field. -/
theorem exists_separable_cubic_line_of_extension_witness
    {K : Type u} {L : Type v} [Field K] [Field L]
    [CharZero K] [CharZero L] [Infinite K]
    (f : K →+* L) (c : Cubic K 4)
    (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0)
    (a b : Fin 4 → L) (ha : (c.map f).eval a ≠ 0)
    (hsep : (AllCharacteristics.cubicLinePolynomial (c.map f) a b).Separable) :
    ∃ a b : Fin 4 → K,
      c.eval a ≠ 0 ∧
        (AllCharacteristics.cubicLinePolynomial c a b).Separable := by
  let det : MvPolynomial GenericCubicLineParameters K := 1
  let base := genericCubicLineBase K
  let direction : Unit → Fin 4 → MvPolynomial GenericCubicLineParameters K :=
    fun _ => genericCubicLineDirection K
  have hbase : (c.map MvPolynomial.C).eval base ≠ 0 :=
    genericCubicLine_baseEvaluation_ne_zero c hc
  have hdisc : ∀ i,
      (parameterizedCubicLinePolynomial c base (direction i)).discr ≠ 0 := by
    intro i
    exact genericCubicLine_discr_ne_zero_of_extension_witness f c hc a b ha hsep
  obtain ⟨x, -, hxbase, hxsep⟩ :=
    exists_parameter_with_det_ne_zero_and_cubicLines_separable
      c det base direction one_ne_zero hbase hdisc
  exact ⟨(fun j => MvPolynomial.eval x (base j)),
    (fun j => MvPolynomial.eval x (direction default j)),
    hxbase, hxsep default⟩

/-- A nonzero smooth cubic over an algebraically closed field has an explicit
smooth homogeneous coordinate point. -/
theorem exists_smooth_cubic_coordinate_point_of_algClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ p : Fin 4 → K, IsSmoothCubicCoordinatePoint c.toMvPolynomial p := by
  classical
  letI : Infinite K := inferInstance
  obtain ⟨a, hFa, ha0⟩ := exists_cubic_nonzero_in_first_chart F hF hF0
  have hca : c.eval a ≠ 0 := by
    have h := Cubic.eval_toMvPolynomial (RingHom.id K) c a
    have hmap : c.map (RingHom.id K) = c := by funext i; rfl
    rw [hmap, hc] at h
    intro hzero
    apply hFa
    simpa using h.trans hzero
  let b : Fin 4 → K := Pi.single 1 1
  let P := AllCharacteristics.cubicLinePolynomial c a b
  have hPdegree : P.degree = 3 := by
    apply (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr
    exact AllCharacteristics.cubicLinePolynomial_natDegree c a b hca
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root P (by rw [hPdegree]; decide)
  let p : Fin 4 → K := t • a + b
  have hp : c.eval p = 0 := by
    have hroot : P.eval₂ (RingHom.id K) t = 0 := by simpa [IsRoot.def] using ht
    rw [show P = AllCharacteristics.cubicLinePolynomial c a b by rfl,
      AllCharacteristics.cubicLinePolynomial_eval₂] at hroot
    have hmap : c.map (RingHom.id K) = c := by funext i; rfl
    simpa [p, hmap] using hroot
  have hp0 : p ≠ 0 := by
    intro hzero
    have hzero0 := congrFun hzero 0
    have ht0 : t = 0 := by
      change t * a 0 + b 0 = 0 at hzero0
      have hmul : t * a 0 = 0 := by simpa [b] using hzero0
      exact (mul_eq_zero.mp hmul).resolve_right ha0
    have hzero1 := congrFun hzero 1
    subst t
    have hone : (1 : K) = 0 := by simpa [p, b] using hzero1
    exact one_ne_zero hone
  obtain ⟨j, hpj⟩ : ∃ j : Fin 4, p j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hp0 (funext hn)
  let y : Fin 4 → K := (p j)⁻¹ • p
  have hyj : y j = 1 := by simp [y, hpj]
  have hy0 : y ≠ 0 := by
    intro hzero
    have h := congrFun hzero j
    simpa [hyj] using h
  have hcy : c.eval y = 0 := by
    rw [show y = (p j)⁻¹ • p by rfl, Cubic.eval_smul, hp, mul_zero]
  have hFy : F.eval y = 0 := by
    have h := Cubic.eval_toMvPolynomial (RingHom.id K) c y
    have hmap : c.map (RingHom.id K) = c := by funext i; rfl
    rw [hmap, hc] at h
    simpa using h.trans hcy
  let I := equationIdeal F hF
  have he : ∀ q ∈ I.toIdeal,
      q.eval₂ (algebraMap K K) y = 0 := by
    intro q hq
    change q ∈ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)) at hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    rw [MvPolynomial.eval₂_mul]
    have hFy' : F.eval₂ (algebraMap K K) y = 0 := by simpa using hFy
    rw [hFy', zero_mul]
  let ev : ChartRing I j →+* K := normalizedPointChartMap I y j hyj he
  have htop : Ideal.span (Set.range (fun i : Fin 4 =>
      (pderiv i F).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤ := by
    simpa [I] using smoothCubic_chartJacobian_top F hF hF0 j
  have hderiv : ∃ i : Fin 4, (pderiv i F).eval y ≠ 0 := by
    by_contra hn
    push Not at hn
    have hgen : ∀ i : Fin 4, ev
        ((pderiv i F).eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0 := by
      intro i
      dsimp [ev]
      rw [normalizedPointChartMap_eval]
      simpa using hn i
    have hle : Ideal.span (Set.range (fun i : Fin 4 =>
        (pderiv i F).eval₂ (chartBaseMap I j) (chartCoordinate I j))) ≤
        RingHom.ker ev := by
      apply Ideal.span_le.mpr
      intro z hz
      obtain ⟨i, rfl⟩ := hz
      exact RingHom.mem_ker.mpr (hgen i)
    have honeMem : (1 : ChartRing I j) ∈ RingHom.ker ev := by
      apply hle
      rw [htop]
      exact Submodule.mem_top
    have hone : (1 : K) = 0 := by
      simpa using RingHom.mem_ker.mp honeMem
    exact one_ne_zero hone
  refine ⟨y, hy0, ?_, ?_⟩
  · simpa [hc] using hFy
  · simpa [hc] using hderiv

/-- Every smooth nonzero cubic surface over a characteristic-zero field has a
transverse affine line section over the ground field.  A transverse line is
first constructed over an algebraic closure; nonvanishing of the universal
line discriminant then descends its existence. -/
theorem exists_separable_cubic_line_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ a b : Fin 4 → K,
      c.eval a ≠ 0 ∧
        (AllCharacteristics.cubicLinePolynomial c a b).Separable := by
  classical
  let L : Type u := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  let F' : MvPolynomial (Fin 4) L := F.map f
  let c' : Cubic L 4 := c.map f
  have hF' : F'.IsHomogeneous 3 := hF.map f
  have hc' : c'.toMvPolynomial = F' := by
    rw [show c'.toMvPolynomial = c.toMvPolynomial.map f by
      exact (cubic_toMvPolynomial_map f c).symm, hc]
  have hF'0 : F' ≠ 0 := by
    intro hzero
    apply hF0
    exact MvPolynomial.map_injective f
      (FaithfulSMul.algebraMap_injective K L) (by simpa [F'] using hzero)
  letI : Smooth (hypersurfaceToBase F' hF') := by
    exact smooth_hypersurfaceToBase_map f F hF
  obtain ⟨p, hp⟩ :=
    exists_smooth_cubic_coordinate_point_of_algClosed F' hF' hF'0 c' hc'
  have hirr : Irreducible F' :=
    irreducible_of_smooth_homogeneous_cubic_of_field F' hF' hF'0
  obtain ⟨a', b', ha', hsep'⟩ :=
    exists_separable_cubic_line_of_irreducible_at_smooth_point
      F' hF' c' hc' hirr p hp
  obtain ⟨v, hv⟩ := exists_vector_eval_ne_zero_of_homogeneous F hF hF0
  have hcv : c.eval v ≠ 0 := by
    have h := Cubic.eval_toMvPolynomial (RingHom.id K) c v
    have hmap : c.map (RingHom.id K) = c := by funext i; rfl
    rw [hmap, hc] at h
    intro hzero
    apply hv
    simpa using h.trans hzero
  exact exists_separable_cubic_line_of_extension_witness
    f c ⟨v, hcv⟩ a' b' ha' hsep'

/-- A smooth nonzero cubic admits one invertible coordinate change for which
all four standard transported line sections are separable. -/
theorem exists_invertible_change_with_four_separable_cubic_lines_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ x : FourLineChangeParameters → K,
      MvPolynomial.eval x (universalFourLineChangeMatrix K).det ≠ 0 ∧
      c.eval (fun j => MvPolynomial.eval x
        (universalChangedFourLineBase K j)) ≠ 0 ∧
      ∀ q : Fin 2 × Fin 2,
        (AllCharacteristics.cubicLinePolynomial c
          (fun j => MvPolynomial.eval x
            (universalChangedFourLineBase K j))
          (fun j => MvPolynomial.eval x
            (universalChangedFourLineDirection K q.1 q.2 j))).Separable := by
  exact exists_invertible_change_with_four_separable_cubic_lines_of_one K c
    (exists_separable_cubic_line_of_smooth F hF hF0 c hc)

theorem exists_strongFourLineChangeWitness_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ x : FourLineChangeParameters → K,
      StrongFourLineChangeWitness K c x := by
  exact exists_invertible_change_with_four_separable_nonzero_cubic_lines_of_one K c
    (exists_separable_cubic_line_of_smooth F hF hF0 c hc)

/-- Coordinate-change form of the four-line conclusion: after one invertible
linear substitution, the four standard split-quadric lines all meet the cubic
transversely. -/
theorem exists_linear_change_with_standard_four_separable_lines_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ M : Matrix (Fin 4) (Fin 4) K,
      IsUnit M.det ∧
      (c.compLinear M).eval (Pi.single 0 1) ≠ 0 ∧
      ∀ q : Fin 2 × Fin 2,
        (AllCharacteristics.cubicLinePolynomial (c.compLinear M)
          (Pi.single 0 1) (lineDirection q.1 q.2)).Separable := by
  obtain ⟨x, hxdet, hxbase, hxsep⟩ :=
    exists_invertible_change_with_four_separable_cubic_lines_of_smooth
      F hF hF0 c hc
  let M : Matrix (Fin 4) (Fin 4) K := fun i j => x (i, j)
  have hMdet : M.det ≠ 0 := by
    let φ := MvPolynomial.eval₂Hom (RingHom.id K) x
    have hmatrix : (universalFourLineChangeMatrix K).map φ = M := by
      ext i j
      simp [universalFourLineChangeMatrix, M, φ]
    have hdetmap : ((universalFourLineChangeMatrix K).map φ).det =
        φ (universalFourLineChangeMatrix K).det := by
      change (φ.mapMatrix (universalFourLineChangeMatrix K)).det = _
      exact (RingHom.map_det φ (universalFourLineChangeMatrix K)).symm
    rw [← hmatrix] 
    rw [hdetmap]
    simpa [φ] using hxdet
  have hbasevec : M.mulVec (Pi.single 0 1) =
      (fun j => MvPolynomial.eval x (universalChangedFourLineBase K j)) := by
    funext i
    exact (universalChangedFourLineBase_eval K x i).symm
  refine ⟨M, (isUnit_iff_ne_zero.mpr hMdet), ?_, ?_⟩
  · rw [Cubic.eval_compLinear]
    rw [hbasevec]
    exact hxbase
  · intro q
    have hdir : M.mulVec (lineDirection q.1 q.2) =
        (fun j => MvPolynomial.eval x
          (universalChangedFourLineDirection K q.1 q.2 j)) := by
      funext i
      exact (universalChangedFourLineDirection_eval K x q.1 q.2 i).symm
    rw [cubicLinePolynomial_compLinear]
    rw [hbasevec, hdir]
    exact hxsep q

/-- The strengthened coordinate form also keeps every standard direction
outside the transformed cubic. -/
theorem exists_linear_change_with_standard_four_separable_nonzero_lines_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ M : Matrix (Fin 4) (Fin 4) K,
      IsUnit M.det ∧
      (c.compLinear M).eval (Pi.single 0 1) ≠ 0 ∧
      (∀ q : Fin 2 × Fin 2,
        (c.compLinear M).eval (lineDirection q.1 q.2) ≠ 0) ∧
      ∀ q : Fin 2 × Fin 2,
        (AllCharacteristics.cubicLinePolynomial (c.compLinear M)
          (Pi.single 0 1) (lineDirection q.1 q.2)).Separable := by
  obtain ⟨x, hxdet, hxbase, hxdir, hxsep⟩ :=
    exists_strongFourLineChangeWitness_of_smooth F hF hF0 c hc
  let M : Matrix (Fin 4) (Fin 4) K := fun i j => x (i, j)
  have hMdet : M.det ≠ 0 := by
    let φ := MvPolynomial.eval₂Hom (RingHom.id K) x
    have hmatrix : (universalFourLineChangeMatrix K).map φ = M := by
      ext i j
      simp [universalFourLineChangeMatrix, M, φ]
    have hdetmap : ((universalFourLineChangeMatrix K).map φ).det =
        φ (universalFourLineChangeMatrix K).det := by
      change (φ.mapMatrix (universalFourLineChangeMatrix K)).det = _
      exact (RingHom.map_det φ (universalFourLineChangeMatrix K)).symm
    rw [← hmatrix, hdetmap]
    simpa [φ] using hxdet
  have hbasevec : M.mulVec (Pi.single 0 1) =
      (fun j => MvPolynomial.eval x (universalChangedFourLineBase K j)) := by
    funext i
    exact (universalChangedFourLineBase_eval K x i).symm
  have hdirvec : ∀ q : Fin 2 × Fin 2,
      M.mulVec (lineDirection q.1 q.2) =
        (fun j => MvPolynomial.eval x
          (universalChangedFourLineDirection K q.1 q.2 j)) := by
    intro q
    funext i
    exact (universalChangedFourLineDirection_eval K x q.1 q.2 i).symm
  refine ⟨M, isUnit_iff_ne_zero.mpr hMdet, ?_, ?_, ?_⟩
  · rw [Cubic.eval_compLinear, hbasevec]
    exact hxbase
  · intro q
    rw [Cubic.eval_compLinear, hdirvec q]
    exact hxdir q
  · intro q
    rw [cubicLinePolynomial_compLinear, hbasevec, hdirvec q]
    exact hxsep q

end PfaffianDescent
