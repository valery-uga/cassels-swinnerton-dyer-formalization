import AllCharacteristics.AlgebraicExtensionTransfiniteDVRLift
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
import Mathlib.SetTheory.Ordinal.Arithmetic

namespace AllCharacteristics.TransfiniteDVRLiftPrefix

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]


structure CompatiblePrefixFamily {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) where
  tower : ∀ b : Set.Iio a, TransfiniteDVRLiftPrefix (K := K) e b.1
  restrict_eq : ∀ b c : Set.Iio a, ∀ h : b ≤ c,
    restrict (tower c) b.1 h = tower b

noncomputable def limitFamilyNext {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {a : ι} (ha : Order.IsSuccLimit a) (i : Set.Iio a) : Set.Iio a :=
  ⟨Order.succ i.1, ha.succ_lt i.2⟩

noncomputable def limitFamilyLift {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a) (i : Set.Iio a) :
    CompleteCharZeroDVRLiftWithUniformizer (transfiniteStageField (K := K) e i.1) :=
  (F.tower (limitFamilyNext ha i)).lift
    ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt i.2)⟩

theorem limitFamilyLift_eq_in_prefix {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (i j : Set.Iio a) (hij : i ≤ j) :
    limitFamilyLift ha F i =
      (F.tower (limitFamilyNext ha j)).lift
        ⟨i.1, lt_of_le_of_lt hij
          (Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2))⟩ := by
  let ni := limitFamilyNext ha i
  let nj := limitFamilyNext ha j
  have hn : ni ≤ nj := Order.succ_le_succ hij
  have hP := F.restrict_eq ni nj hn
  have hlocal :
      (restrict (F.tower nj) ni.1 hn).lift
          ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt i.2)⟩ =
        (F.tower ni).lift
          ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt i.2)⟩ :=
    congrArg (fun P => P.lift
      ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt i.2)⟩) hP
  exact hlocal.symm

noncomputable def limitFamilyInclusion {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a) :
    ∀ i j (h : i ≤ j),
      letI : CommRing (limitFamilyLift ha F i).lift.R :=
        (limitFamilyLift ha F i).lift.commRing
      letI : CommRing (limitFamilyLift ha F j).lift.R :=
        (limitFamilyLift ha F j).lift.commRing
      (limitFamilyLift ha F i).lift.R →+* (limitFamilyLift ha F j).lift.R := by
  intro i j hij
  let Pj := F.tower (limitFamilyNext ha j)
  let i' : Set.Iio (limitFamilyNext ha j).1 :=
    ⟨i.1, lt_of_le_of_lt hij
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2))⟩
  let j' : Set.Iio (limitFamilyNext ha j).1 :=
    ⟨j.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2)⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F i j hij)
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F j j le_rfl)
  exact eJ.symm.toRingHom.comp ((Pj.inclusion i' j' hij).comp eI.toRingHom)

end AllCharacteristics.TransfiniteDVRLiftPrefix

namespace AllCharacteristics.TransfiniteDVRLiftPrefix

noncomputable def limitFamilyInclusionAt {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (i j k : Set.Iio a) (hij : i ≤ j) (hjk : j ≤ k) :
    letI : CommRing (limitFamilyLift ha F i).lift.R :=
      (limitFamilyLift ha F i).lift.commRing
    letI : CommRing (limitFamilyLift ha F j).lift.R :=
      (limitFamilyLift ha F j).lift.commRing
    (limitFamilyLift ha F i).lift.R →+* (limitFamilyLift ha F j).lift.R := by
  let Pk := F.tower (limitFamilyNext ha k)
  let i' : Set.Iio (limitFamilyNext ha k).1 :=
    ⟨i.1, lt_of_le_of_lt (hij.trans hjk)
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt k.2))⟩
  let j' : Set.Iio (limitFamilyNext ha k).1 :=
    ⟨j.1, lt_of_le_of_lt hjk
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt k.2))⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F i k (hij.trans hjk))
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F j k hjk)
  exact eJ.symm.toRingHom.comp ((Pk.inclusion i' j' hij).comp eI.toRingHom)

theorem restrict_inclusion_heq {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] {e : ι → L} {b c : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e c)
    (Q : TransfiniteDVRLiftPrefix (K := K) e b) (hbc : b ≤ c)
    (hPQ : restrict P b hbc = Q)
    (i j : Set.Iio b) (hij : i ≤ j) :
    HEq (P.inclusion
      ⟨i.1, i.2.trans_le hbc⟩ ⟨j.1, j.2.trans_le hbc⟩ hij)
      (Q.inclusion i j hij) := by
  subst Q
  rfl

theorem transportedRingHom_eq_of_heq
    {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (E A A' : CompleteCharZeroDVRLiftWithUniformizer k₁)
    (F B B' : CompleteCharZeroDVRLiftWithUniformizer k₂)
    (hA : E = A) (hB : F = B) (hA' : E = A') (hB' : F = B') :
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k₁, CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k₂, CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    ∀ (f : A.lift.R →+* B.lift.R) (g : A'.lift.R →+* B'.lift.R), HEq f g →
      (RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k₂ => Q.lift.R) hB).symm.toRingHom.comp
          (f.comp (RingEquiv.cast
            (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k₁ => Q.lift.R) hA).toRingHom) =
      (RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k₂ => Q.lift.R) hB').symm.toRingHom.comp
          (g.comp (RingEquiv.cast
            (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k₁ => Q.lift.R) hA').toRingHom) := by
  subst A
  subst B
  subst A'
  subst B'
  intro f g hfg
  exact eq_of_heq hfg

theorem limitFamilyInclusion_eq_at {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (i j k : Set.Iio a) (hij : i ≤ j) (hjk : j ≤ k) :
    limitFamilyInclusion ha F i j hij =
      limitFamilyInclusionAt ha F i j k hij hjk := by
  classical
  let nj := limitFamilyNext ha j
  let nk := limitFamilyNext ha k
  let Pj := F.tower nj
  let Pk := F.tower nk
  let iJ : Set.Iio nj.1 :=
    ⟨i.1, lt_of_le_of_lt hij
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2))⟩
  let jJ : Set.Iio nj.1 :=
    ⟨j.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2)⟩
  let iK : Set.Iio nk.1 :=
    ⟨i.1, lt_of_le_of_lt (hij.trans hjk)
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt k.2))⟩
  let jK : Set.Iio nk.1 :=
    ⟨j.1, lt_of_le_of_lt hjk
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt k.2))⟩
  have hnk : nj ≤ nk := Order.succ_le_succ hjk
  have hP := F.restrict_eq nj nk hnk
  have hmap : HEq (Pj.inclusion iJ jJ hij) (Pk.inclusion iK jK hij) := by
    symm
    exact restrict_inclusion_heq Pk Pj hnk hP iJ jJ hij
  unfold limitFamilyInclusion limitFamilyInclusionAt
  exact transportedRingHom_eq_of_heq
    (limitFamilyLift ha F i) (Pj.lift iJ) (Pk.lift iK)
    (limitFamilyLift ha F j) (Pj.lift jJ) (Pk.lift jK)
    (limitFamilyLift_eq_in_prefix ha F i j hij)
    (limitFamilyLift_eq_in_prefix ha F j j le_rfl)
    (limitFamilyLift_eq_in_prefix ha F i k (hij.trans hjk))
    (limitFamilyLift_eq_in_prefix ha F j k hjk)
    (Pj.inclusion iJ jJ hij) (Pk.inclusion iK jK hij) hmap

end AllCharacteristics.TransfiniteDVRLiftPrefix

namespace AllCharacteristics.TransfiniteDVRLiftPrefix

theorem limitFamilyInclusion_injective {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (i j : Set.Iio a) (hij : i ≤ j) :
    letI : CommRing (limitFamilyLift ha F i).lift.R :=
      (limitFamilyLift ha F i).lift.commRing
    letI : CommRing (limitFamilyLift ha F j).lift.R :=
      (limitFamilyLift ha F j).lift.commRing
    Function.Injective (limitFamilyInclusion ha F i j hij) := by
  let Pj := F.tower (limitFamilyNext ha j)
  let i' : Set.Iio (limitFamilyNext ha j).1 :=
    ⟨i.1, lt_of_le_of_lt hij
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2))⟩
  let j' : Set.Iio (limitFamilyNext ha j).1 :=
    ⟨j.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2)⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F i j hij)
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F j j le_rfl)
  unfold limitFamilyInclusion
  change Function.Injective
    (eJ.symm.toRingHom.comp ((Pj.inclusion i' j' hij).comp eI.toRingHom))
  exact eJ.symm.injective.comp ((Pj.inclusion_injective i' j' hij).comp eI.injective)

theorem limitFamilyInclusion_self {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a) (i : Set.Iio a) :
    letI : CommRing (limitFamilyLift ha F i).lift.R :=
      (limitFamilyLift ha F i).lift.commRing
    limitFamilyInclusion ha F i i le_rfl = RingHom.id _ := by
  rw [limitFamilyInclusion_eq_at ha F i i i le_rfl le_rfl]
  let Pi := F.tower (limitFamilyNext ha i)
  let i' : Set.Iio (limitFamilyNext ha i).1 :=
    ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt i.2)⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F i i le_rfl)
  unfold limitFamilyInclusionAt
  change eI.symm.toRingHom.comp ((Pi.inclusion i' i' le_rfl).comp eI.toRingHom) =
    RingHom.id _
  rw [Pi.inclusion_self]
  ext x
  exact eI.symm_apply_apply x

end AllCharacteristics.TransfiniteDVRLiftPrefix

namespace AllCharacteristics.TransfiniteDVRLiftPrefix

theorem limitFamilyInclusion_comp {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (i j k : Set.Iio a) (hij : i ≤ j) (hjk : j ≤ k) :
    letI : CommRing (limitFamilyLift ha F i).lift.R :=
      (limitFamilyLift ha F i).lift.commRing
    letI : CommRing (limitFamilyLift ha F j).lift.R :=
      (limitFamilyLift ha F j).lift.commRing
    letI : CommRing (limitFamilyLift ha F k).lift.R :=
      (limitFamilyLift ha F k).lift.commRing
    (limitFamilyInclusion ha F j k hjk).comp
        (limitFamilyInclusion ha F i j hij) =
      limitFamilyInclusion ha F i k (hij.trans hjk) := by
  rw [limitFamilyInclusion_eq_at ha F i j k hij hjk]
  rw [limitFamilyInclusion_eq_at ha F j k k hjk le_rfl]
  rw [limitFamilyInclusion_eq_at ha F i k k (hij.trans hjk) le_rfl]
  let Pk := F.tower (limitFamilyNext ha k)
  let i' : Set.Iio (limitFamilyNext ha k).1 :=
    ⟨i.1, lt_of_le_of_lt (hij.trans hjk)
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt k.2))⟩
  let j' : Set.Iio (limitFamilyNext ha k).1 :=
    ⟨j.1, lt_of_le_of_lt hjk
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt k.2))⟩
  let k' : Set.Iio (limitFamilyNext ha k).1 :=
    ⟨k.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt k.2)⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e k.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F i k (hij.trans hjk))
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F j k hjk)
  let eK := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e k.1) => Q.lift.R)
    (limitFamilyLift_eq_in_prefix ha F k k le_rfl)
  unfold limitFamilyInclusionAt
  ext x
  change eK.symm (Pk.inclusion j' k' hjk
      (eJ (eJ.symm (Pk.inclusion i' j' hij (eI x))))) =
    eK.symm (Pk.inclusion i' k' (hij.trans hjk) (eI x))
  rw [eJ.apply_symm_apply]
  exact congrArg eK.symm (by
    simpa only [RingHom.comp_apply] using
      congrArg (fun f => f (eI x)) (Pk.inclusion_comp i' j' k' hij hjk))

end AllCharacteristics.TransfiniteDVRLiftPrefix

namespace AllCharacteristics.TransfiniteDVRLiftPrefix

theorem limitFamilyInclusion_uniformizer {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (i j : Set.Iio a) (hij : i ≤ j) :
    letI : CommRing (limitFamilyLift ha F i).lift.R :=
      (limitFamilyLift ha F i).lift.commRing
    letI : CommRing (limitFamilyLift ha F j).lift.R :=
      (limitFamilyLift ha F j).lift.commRing
    limitFamilyInclusion ha F i j hij (limitFamilyLift ha F i).uniformizer =
      (limitFamilyLift ha F j).uniformizer := by
  let Pj := F.tower (limitFamilyNext ha j)
  let i' : Set.Iio (limitFamilyNext ha j).1 :=
    ⟨i.1, lt_of_le_of_lt hij
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2))⟩
  let j' : Set.Iio (limitFamilyNext ha j).1 :=
    ⟨j.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2)⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  let hI := limitFamilyLift_eq_in_prefix ha F i j hij
  let hJ := limitFamilyLift_eq_in_prefix ha F j j le_rfl
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R) hI
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1) => Q.lift.R) hJ
  unfold limitFamilyInclusion
  change eJ.symm (Pj.inclusion i' j' hij (eI _)) = _
  have hIu := ringEquiv_cast_uniformizer (limitFamilyLift ha F i) (Pj.lift i') hI
  have hJu := ringEquiv_cast_uniformizer (limitFamilyLift ha F j) (Pj.lift j') hJ
  rw [hIu, Pj.uniformizer_maps i' j' hij]
  apply eJ.injective
  simpa [eJ, j'] using hJu.symm

theorem limitFamilyInclusion_residue {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (i j : Set.Iio a) (hij : i ≤ j)
    (x : (limitFamilyLift ha F i).lift.R) :
    letI : CommRing (limitFamilyLift ha F i).lift.R :=
      (limitFamilyLift ha F i).lift.commRing
    letI : CommRing (limitFamilyLift ha F j).lift.R :=
      (limitFamilyLift ha F j).lift.commRing
    (limitFamilyLift ha F j).lift.residue
        (limitFamilyInclusion ha F i j hij x) =
      transfiniteStageFieldInclusion (K := K) e hij
        ((limitFamilyLift ha F i).lift.residue x) := by
  let Pj := F.tower (limitFamilyNext ha j)
  let i' : Set.Iio (limitFamilyNext ha j).1 :=
    ⟨i.1, lt_of_le_of_lt hij
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2))⟩
  let j' : Set.Iio (limitFamilyNext ha j).1 :=
    ⟨j.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt j.2)⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  let hI := limitFamilyLift_eq_in_prefix ha F i j hij
  let hJ := limitFamilyLift_eq_in_prefix ha F j j le_rfl
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R) hI
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1) => Q.lift.R) hJ
  unfold limitFamilyInclusion
  change (limitFamilyLift ha F j).lift.residue
    (eJ.symm (Pj.inclusion i' j' hij (eI x))) = _
  rw [ringEquiv_cast_symm_residue _ _ hJ]
  rw [Pj.residue_commutes i' j' hij]
  rw [ringEquiv_cast_residue _ _ hI]

noncomputable def ofCompatibleFamily {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a) :
    TransfiniteDVRLiftPrefix (K := K) e a := {
  lift := limitFamilyLift ha F
  inclusion := limitFamilyInclusion ha F
  inclusion_injective := limitFamilyInclusion_injective ha F
  inclusion_self := limitFamilyInclusion_self ha F
  inclusion_comp := limitFamilyInclusion_comp ha F
  residue_commutes := limitFamilyInclusion_residue ha F
  uniformizer_maps := limitFamilyInclusion_uniformizer ha F
}

end AllCharacteristics.TransfiniteDVRLiftPrefix

namespace AllCharacteristics.TransfiniteDVRLiftPrefix

theorem limitFamilyLift_eq_in_tower {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (b : Set.Iio a) (i : Set.Iio b.1) :
    limitFamilyLift ha F ⟨i.1, i.2.trans b.2⟩ = (F.tower b).lift i := by
  let ni := limitFamilyNext ha (⟨i.1, i.2.trans b.2⟩ : Set.Iio a)
  have hn : ni ≤ b := Order.succ_le_of_lt i.2
  have hP := F.restrict_eq ni b hn
  have hlocal :
      (restrict (F.tower b) ni.1 hn).lift
          ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt (i.2.trans b.2))⟩ =
        (F.tower ni).lift
          ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt (i.2.trans b.2))⟩ :=
    congrArg (fun P => P.lift
      ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt (i.2.trans b.2))⟩) hP
  exact hlocal.symm

noncomputable def limitFamilyInclusionBelow {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (b : Set.Iio a) (i j : Set.Iio b.1) (hij : i ≤ j) :
    let iA : Set.Iio a := ⟨i.1, i.2.trans b.2⟩
    let jA : Set.Iio a := ⟨j.1, j.2.trans b.2⟩
    letI : CommRing (limitFamilyLift ha F iA).lift.R :=
      (limitFamilyLift ha F iA).lift.commRing
    letI : CommRing (limitFamilyLift ha F jA).lift.R :=
      (limitFamilyLift ha F jA).lift.commRing
    (limitFamilyLift ha F iA).lift.R →+* (limitFamilyLift ha F jA).lift.R := by
  dsimp only
  let Pb := F.tower b
  let iA : Set.Iio a := ⟨i.1, i.2.trans b.2⟩
  let jA : Set.Iio a := ⟨j.1, j.2.trans b.2⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R)
    (limitFamilyLift_eq_in_tower ha F b i)
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1) => Q.lift.R)
    (limitFamilyLift_eq_in_tower ha F b j)
  exact eJ.symm.toRingHom.comp ((Pb.inclusion i j hij).comp eI.toRingHom)

theorem limitFamilyInclusion_eq_below {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a)
    (b : Set.Iio a) (i j : Set.Iio b.1) (hij : i ≤ j) :
    limitFamilyInclusion ha F
        ⟨i.1, i.2.trans b.2⟩ ⟨j.1, j.2.trans b.2⟩ hij =
      limitFamilyInclusionBelow ha F b i j hij := by
  classical
  let jA : Set.Iio a := ⟨j.1, j.2.trans b.2⟩
  let nj := limitFamilyNext ha jA
  let Pj := F.tower nj
  let Pb := F.tower b
  let iJ : Set.Iio nj.1 :=
    ⟨i.1, lt_of_le_of_lt hij
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt jA.2))⟩
  let jJ : Set.Iio nj.1 :=
    ⟨j.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt jA.2)⟩
  have hnb : nj ≤ b := Order.succ_le_of_lt j.2
  have hP := F.restrict_eq nj b hnb
  have hmap : HEq (Pj.inclusion iJ jJ hij) (Pb.inclusion i j hij) := by
    symm
    exact restrict_inclusion_heq Pb Pj hnb hP iJ jJ hij
  unfold limitFamilyInclusion limitFamilyInclusionBelow
  exact transportedRingHom_eq_of_heq
    (limitFamilyLift ha F ⟨i.1, i.2.trans b.2⟩) (Pj.lift iJ) (Pb.lift i)
    (limitFamilyLift ha F ⟨j.1, j.2.trans b.2⟩) (Pj.lift jJ) (Pb.lift j)
    (limitFamilyLift_eq_in_prefix ha F
      ⟨i.1, i.2.trans b.2⟩ ⟨j.1, j.2.trans b.2⟩ hij)
    (limitFamilyLift_eq_in_prefix ha F
      ⟨j.1, j.2.trans b.2⟩ ⟨j.1, j.2.trans b.2⟩ le_rfl)
    (limitFamilyLift_eq_in_tower ha F b i)
    (limitFamilyLift_eq_in_tower ha F b j)
    (Pj.inclusion iJ jJ hij) (Pb.inclusion i j hij) hmap

theorem restrict_ofCompatibleFamily {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    {e : ι → L} {a : ι} (ha : Order.IsSuccLimit a)
    (F : CompatiblePrefixFamily (K := K) e a) (b : Set.Iio a) :
    restrict (ofCompatibleFamily ha F) b.1 b.2.le = F.tower b := by
  classical
  apply ext_pointwise
  · intro i
    exact limitFamilyLift_eq_in_tower ha F b i
  · intro i j hij
    change HEq
      (limitFamilyInclusion ha F
        ⟨i.1, i.2.trans b.2⟩ ⟨j.1, j.2.trans b.2⟩ hij)
      ((F.tower b).inclusion i j hij)
    rw [limitFamilyInclusion_eq_below ha F b i j hij]
    unfold limitFamilyInclusionBelow
    exact transportedRingHom_heq
      (limitFamilyLift ha F ⟨i.1, i.2.trans b.2⟩) ((F.tower b).lift i)
      (limitFamilyLift ha F ⟨j.1, j.2.trans b.2⟩) ((F.tower b).lift j)
      (limitFamilyLift_eq_in_tower ha F b i)
      (limitFamilyLift_eq_in_tower ha F b j)
      ((F.tower b).inclusion i j hij)

end AllCharacteristics.TransfiniteDVRLiftPrefix

open CategoryTheory
namespace AllCharacteristics.TransfiniteDVRLiftPrefix

noncomputable def restrictionFunctor {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] (e : ι → L) : ιᵒᵖ ⥤ Type (u + 1) where
  obj a := TransfiniteDVRLiftPrefix (K := K) e a.unop
  map {X Y} f := ↾fun P =>
    restrict (K := K) (e := e) P Y.unop f.unop.le
  map_id X := by
    ext P
    exact restrict_self P
  map_comp f g := by
    ext P
    exact (restrict_trans P g.unop.le f.unop.le).symm

noncomputable def compatibleFamilyOfSection {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] (e : ι → L) (a : ι)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio a)).monotone.functor.op ⋙
      restrictionFunctor (K := K) e).sections) :
    CompatiblePrefixFamily (K := K) e a where
  tower b := by
    exact x.val (.op b)
  restrict_eq b c h := by
    change restrict (x.val (.op c)) b.1 h = x.val (.op b)
    have hx := x.property (homOfLE h).op
    change restrict (x.val (.op c)) b.1 h = x.val (.op b) at hx
    exact hx

end AllCharacteristics.TransfiniteDVRLiftPrefix

open CategoryTheory
namespace AllCharacteristics.TransfiniteDVRLiftPrefix

noncomputable def wellOrderInductionData {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (hK : HasCompleteCharZeroDVRLift K) :
    (restrictionFunctor (K := K) e).WellOrderInductionData where
  succ j hj P := extendPrefix e hK j hj P
  map_succ j hj P := by
    change restrict (extendPrefix e hK j hj P) j (Order.le_succ j) = P
    exact restrict_successorPrefix e j hj P
      (stageData e hK j P).lift (stageData e hK j P).cocone
  lift j hj x := ofCompatibleFamily hj (compatibleFamilyOfSection e j x)
  map_lift j hj x i hi := by
    change restrict (ofCompatibleFamily hj (compatibleFamilyOfSection e j x)) i hi.le =
      x.val (.op ⟨i, hi⟩)
    exact restrict_ofCompatibleFamily hj (compatibleFamilyOfSection e j x) ⟨i, hi⟩

noncomputable def globalPrefixSection {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [WellFoundedLT ι]
    [Algebra.IsAlgebraic K L]
    (e : ι → L) (hK : HasCompleteCharZeroDVRLift K) :
    (restrictionFunctor (K := K) e).sections :=
  (wellOrderInductionData e hK).sectionsMk (minPrefix e ⊥ isMin_bot)

noncomputable def globalPrefix {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [WellFoundedLT ι]
    [Algebra.IsAlgebraic K L]
    (e : ι → L) (hK : HasCompleteCharZeroDVRLift K) (a : ι) :
    TransfiniteDVRLiftPrefix (K := K) e a :=
  (globalPrefixSection e hK).val (.op a)

theorem globalPrefix_restrict {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [WellFoundedLT ι]
    [Algebra.IsAlgebraic K L]
    (e : ι → L) (hK : HasCompleteCharZeroDVRLift K) {a b : ι} (hba : b ≤ a) :
    restrict (globalPrefix e hK a) b hba = globalPrefix e hK b := by
  have h := (globalPrefixSection e hK).property (homOfLE hba).op
  change restrict (globalPrefix e hK a) b hba = globalPrefix e hK b at h
  exact h

end AllCharacteristics.TransfiniteDVRLiftPrefix

namespace AllCharacteristics.TransfiniteDVRLiftPrefix

theorem hasCompleteCharZeroDVRLift_of_top_stage {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    {ι : Type u} [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [SuccOrder ι] [WellFoundedLT ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (hK : HasCompleteCharZeroDVRLift K)
    (htop : transfiniteStageField (K := K) e ⊤ = ⊤) :
    HasCompleteCharZeroDVRLift L := by
  let P := globalPrefix e hK ⊤
  let D := (stageData e hK ⊤ P).lift.lift
  have hD : HasCompleteCharZeroDVRLift (transfiniteStageField (K := K) e ⊤) :=
    D.hasCompleteCharZeroDVRLift
  rw [htop] at hD
  exact hD.of_equiv IntermediateField.topEquiv.toRingEquiv

end AllCharacteristics.TransfiniteDVRLiftPrefix

namespace AllCharacteristics

theorem HasCompleteCharZeroDVRLift.algebraic_extension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (hK : HasCompleteCharZeroDVRLift K) : HasCompleteCharZeroDVRLift L := by
  let κ := Cardinal.mk L
  let α := κ.ord.ToType
  letI : Nonempty α := Cardinal.nonempty_ord_toType (Cardinal.mk_ne_zero L)
  letI : OrderBot α := WellFoundedLT.toOrderBot α
  let q : α ≃ L := (Cardinal.eq.mp (Cardinal.mk_ord_toType κ)).some
  let e : WithTop α → L := WithTop.recTopCoe 0 q
  have htop : transfiniteStageField (K := K) e (⊤ : WithTop α) = ⊤ := by
    apply top_unique
    intro x hx
    apply IntermediateField.subset_adjoin K
    refine ⟨(q.symm x : WithTop α), WithTop.coe_lt_top _, ?_⟩
    change q (q.symm x) = x
    exact q.apply_symm_apply x
  exact TransfiniteDVRLiftPrefix.hasCompleteCharZeroDVRLift_of_top_stage e hK htop

end AllCharacteristics
