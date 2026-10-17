import AllCharacteristics.AlgebraicExtensionDVRLiftSteps
import AllCharacteristics.CompleteDVRLiftLimitData

/-!
# Limit steps in an algebraic DVR-lift tower

A prefix retains the complete DVR lifts and compatible ring maps for all
prior field stages.  At a limit ordinal, its directed colimit and completion
produce the retained lift of the limit field.
-/

namespace AllCharacteristics

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The canonical inclusion between two stages of an enumerated field
filtration. -/
noncomputable def transfiniteStageFieldInclusion {ι : Type u} [LinearOrder ι]
    (e : ι → L) {i j : ι} (h : i ≤ j) :
    transfiniteStageField (K := K) e i →+* transfiniteStageField (K := K) e j :=
  (IntermediateField.inclusion (transfiniteStageField_mono e h)).toRingHom

/-- A compatible family of retained complete DVR lifts on all stages below an
ordinal.  Its maps are stored as actual ring maps, with both residue and
uniformizer compatibility retained for the colimit construction. -/
structure TransfiniteDVRLiftPrefix {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) where
  lift : ∀ i : Set.Iio a,
    CompleteCharZeroDVRLiftWithUniformizer (transfiniteStageField (K := K) e i.1)
  inclusion : ∀ i j (h : i ≤ j),
    letI : CommRing (lift i).lift.R := (lift i).lift.commRing
    letI : CommRing (lift j).lift.R := (lift j).lift.commRing
    (lift i).lift.R →+* (lift j).lift.R
  inclusion_injective : ∀ i j (h : i ≤ j),
    letI : CommRing (lift i).lift.R := (lift i).lift.commRing
    letI : CommRing (lift j).lift.R := (lift j).lift.commRing
    Function.Injective (inclusion i j h)
  inclusion_self : ∀ i,
    letI : CommRing (lift i).lift.R := (lift i).lift.commRing
    inclusion i i le_rfl = RingHom.id (lift i).lift.R
  inclusion_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    letI : CommRing (lift i).lift.R := (lift i).lift.commRing
    letI : CommRing (lift j).lift.R := (lift j).lift.commRing
    letI : CommRing (lift k).lift.R := (lift k).lift.commRing
    inclusion j k hjk |>.comp (inclusion i j hij) = inclusion i k (hij.trans hjk)
  residue_commutes : ∀ i j (h : i ≤ j) (r : (lift i).lift.R),
    letI : CommRing (lift i).lift.R := (lift i).lift.commRing
    letI : CommRing (lift j).lift.R := (lift j).lift.commRing
    (lift j).lift.residue (inclusion i j h r) =
      transfiniteStageFieldInclusion (K := K) e h ((lift i).lift.residue r)
  uniformizer_maps : ∀ i j (h : i ≤ j),
    letI : CommRing (lift i).lift.R := (lift i).lift.commRing
    letI : CommRing (lift j).lift.R := (lift j).lift.commRing
    inclusion i j h (lift i).uniformizer = (lift j).uniformizer

/-- A compatible family of maps from a retained prefix into one new DVR lift.
This is the interface shared by successor extensions and by the completion at
a limit stage.  Retaining the commuting triangles here is what allows the
transfinite construction to extend a prefix without losing coherence. -/
structure TransfiniteDVRLiftCocone {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a)) where
  inclusion : ∀ i : Set.Iio a,
    letI : CommRing (P.lift i).lift.R := (P.lift i).lift.commRing
    letI : CommRing D.lift.R := D.lift.commRing
    (P.lift i).lift.R →+* D.lift.R
  inclusion_injective : ∀ i : Set.Iio a,
    letI : CommRing (P.lift i).lift.R := (P.lift i).lift.commRing
    letI : CommRing D.lift.R := D.lift.commRing
    Function.Injective (inclusion i)
  inclusion_comp : ∀ i j (h : i ≤ j) (x : (P.lift i).lift.R),
    letI : CommRing (P.lift i).lift.R := (P.lift i).lift.commRing
    letI : CommRing (P.lift j).lift.R := (P.lift j).lift.commRing
    letI : CommRing D.lift.R := D.lift.commRing
    inclusion j (P.inclusion i j h x) = inclusion i x
  residue_commutes : ∀ i (x : (P.lift i).lift.R),
    letI : CommRing (P.lift i).lift.R := (P.lift i).lift.commRing
    letI : CommRing D.lift.R := D.lift.commRing
    D.lift.residue (inclusion i x) =
      transfiniteStageFieldInclusion (K := K) e i.2.le ((P.lift i).lift.residue x)
  uniformizer_maps : ∀ i,
    letI : CommRing (P.lift i).lift.R := (P.lift i).lift.commRing
    letI : CommRing D.lift.R := D.lift.commRing
    inclusion i (P.lift i).uniformizer = D.uniformizer

/-- A lift at the endpoint of a prefix together with all compatible maps
from the earlier stages into it. -/
structure TransfiniteDVRLiftStageData {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (P : TransfiniteDVRLiftPrefix (K := K) e a) where
  lift : CompleteCharZeroDVRLiftWithUniformizer
    (transfiniteStageField (K := K) e a)
  cocone : TransfiniteDVRLiftCocone e a P lift

end AllCharacteristics

namespace AllCharacteristics.TransfiniteDVRLiftPrefix

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The unique vacuous prefix below a minimal index. -/
noncomputable def minPrefix {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (ha : IsMin a) :
    TransfiniteDVRLiftPrefix (K := K) e a := {
  lift := fun i => (ha.not_lt i.2).elim
  inclusion := fun i => (ha.not_lt i.2).elim
  inclusion_injective := fun i => (ha.not_lt i.2).elim
  inclusion_self := fun i => (ha.not_lt i.2).elim
  inclusion_comp := fun i => (ha.not_lt i.2).elim
  residue_commutes := fun i => (ha.not_lt i.2).elim
  uniformizer_maps := fun i => (ha.not_lt i.2).elim
}

/-- Restrict a retained prefix to any earlier endpoint. -/
noncomputable def restrict {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (b : ι) (hba : b ≤ a) : TransfiniteDVRLiftPrefix (K := K) e b := by
  let inc : Set.Iio b → Set.Iio a := fun i => ⟨i.1, i.2.trans_le hba⟩
  exact {
    lift := fun i => P.lift (inc i)
    inclusion := fun i j hij => P.inclusion (inc i) (inc j) hij
    inclusion_injective := fun i j hij => P.inclusion_injective (inc i) (inc j) hij
    inclusion_self := fun i => P.inclusion_self (inc i)
    inclusion_comp := fun i j k hij hjk => P.inclusion_comp (inc i) (inc j) (inc k) hij hjk
    residue_commutes := fun i j hij x => P.residue_commutes (inc i) (inc j) hij x
    uniformizer_maps := fun i j hij => P.uniformizer_maps (inc i) (inc j) hij
  }

theorem restrict_self {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    restrict P a le_rfl = P := by
  cases P
  rfl

theorem restrict_trans {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a b c : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (hcb : c ≤ b) (hba : b ≤ a) :
    restrict (restrict P b hba) c hcb = restrict P c (hcb.trans hba) := by
  cases P
  rfl

/-- Two prefixes are equal once their retained lifts agree pointwise and
their transition maps agree after the corresponding dependent transports. -/
theorem ext_pointwise {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P Q : TransfiniteDVRLiftPrefix (K := K) e a)
    (hl : ∀ i, P.lift i = Q.lift i)
    (hi : ∀ i j (h : i ≤ j), HEq (P.inclusion i j h) (Q.inclusion i j h)) : P = Q := by
  rcases P with ⟨Plift, Pinc, Pinj, Pself, Pcomp, Pres, Puni⟩
  rcases Q with ⟨Qlift, Qinc, Qinj, Qself, Qcomp, Qres, Quni⟩
  dsimp at hl hi ⊢
  have hlfun : Plift = Qlift := funext hl
  cases hlfun
  have hifun : Pinc = Qinc := by
    funext i j h
    exact eq_of_heq (hi i j h)
  cases hifun
  rfl

/-- Conjugating a ring map by equality transports of its source and target
does not change that map, up to heterogeneous equality. -/
theorem transportedRingHom_heq
    {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (E E' : CompleteCharZeroDVRLiftWithUniformizer k₁)
    (F F' : CompleteCharZeroDVRLiftWithUniformizer k₂)
    (hE : E = E') (hF : F = F') :
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k₁, CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k₂, CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    ∀ f : E'.lift.R →+* F'.lift.R,
    HEq ((RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k₂ => Q.lift.R) hF).symm.toRingHom.comp
      (f.comp (RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k₁ => Q.lift.R) hE).toRingHom)) f := by
  subst E'
  subst F'
  intro f
  rfl

/-- The ring at one stage of a compatible prefix. -/
abbrev ringAt {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) (i : Set.Iio a) : Type u :=
  (P.lift i).lift.R

instance ringAtCommRing {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) (i : Set.Iio a) : CommRing (ringAt P i) :=
  (P.lift i).lift.commRing

instance ringAtDomain {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) (i : Set.Iio a) : IsDomain (ringAt P i) :=
  (P.lift i).lift.domain

instance ringAtDVR {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) (i : Set.Iio a) :
    IsDiscreteValuationRing (ringAt P i) :=
  (P.lift i).lift.dvr

instance ringAtCharZero {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) (i : Set.Iio a) : CharZero (ringAt P i) :=
  (P.lift i).lift.charZero

/-- Transition maps in the ring system retained by a prefix. -/
noncomputable def ringMap {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    ∀ i j (_ : i ≤ j), ringAt P i →+* ringAt P j := fun i j h => P.inclusion i j h

instance ringMapDirectedSystem {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) : DirectedSystem (ringAt P) (ringMap P · · ·) := {
  map_self := by
    intro i x
    change P.inclusion i i le_rfl x = x
    rw [P.inclusion_self]
    rfl
  map_map := by
    intro k j i hij hjk x
    change P.inclusion j k hjk (P.inclusion i j hij x) =
      P.inclusion i k (hij.trans hjk) x
    rw [← RingHom.comp_apply, P.inclusion_comp]
  }

/-- The compatible uniformizers in a prefix. -/
noncomputable def ringUniformizer {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) : ∀ i, ringAt P i :=
  fun i => (P.lift i).uniformizer

theorem ringUniformizer_irreducible {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    ∀ i, Irreducible (ringUniformizer P i) := fun i => (P.lift i).uniformizer_irreducible

theorem ringUniformizer_maps {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    ∀ i j (h : i ≤ j), ringMap P i j h (ringUniformizer P i) = ringUniformizer P j := fun i j h =>
  P.uniformizer_maps i j h

theorem ringMap_injective {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    ∀ i j (h : i ≤ j), Function.Injective (ringMap P i j h) := fun i j h =>
  P.inclusion_injective i j h

/-- The residue map from each ring in a prefix to its limit-stage field. -/
noncomputable def residueToLimit {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    ∀ i, ringAt P i →+* transfiniteStageField (K := K) e a := fun i =>
  (transfiniteStageFieldInclusion (K := K) e i.2.le).comp (P.lift i).lift.residue

theorem residueToLimit_coe {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) (i : Set.Iio a) (y : ringAt P i) :
    ((residueToLimit P i y : transfiniteStageField (K := K) e a) : L) =
      ((P.lift i).lift.residue y : L) := by
  simp only [residueToLimit, RingHom.comp_apply, transfiniteStageFieldInclusion]
  exact IntermediateField.coe_inclusion _ _

theorem residueToLimit_compatible {ι : Type u} [LinearOrder ι] {e : ι → L} {a : ι}
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    ∀ i j (h : i ≤ j) (x : ringAt P i),
      residueToLimit P j (ringMap P i j h x) = residueToLimit P i x := by
  intro i j h x
  change transfiniteStageFieldInclusion (K := K) e j.2.le
    ((P.lift j).lift.residue (P.inclusion i j h x)) =
    transfiniteStageFieldInclusion (K := K) e i.2.le ((P.lift i).lift.residue x)
  rw [P.residue_commutes]
  exact IntermediateField.inclusion_inclusion
    (transfiniteStageField_mono e h)
    (transfiniteStageField_mono e j.2.le) ((P.lift i).lift.residue x)

theorem stageFields_directedBelow {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) : Directed (· ≤ ·) (fun i : Set.Iio a =>
      transfiniteStageField (K := K) e i.1) := by
  intro i j
  refine ⟨⟨max i.1 j.1, max_lt i.2 j.2⟩, ?_, ?_⟩
  · exact transfiniteStageField_mono e (le_max_left _ _)
  · exact transfiniteStageField_mono e (le_max_right _ _)

/-- Every element of a limit-stage field occurs at an earlier stage. -/
theorem exists_mem_stage_of_limit {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a) [Nonempty (Set.Iio a)]
    (x : transfiniteStageField (K := K) e a) :
    ∃ i : Set.Iio a, (x : L) ∈ transfiniteStageField (K := K) e i.1 := by
  have hx : (x : L) ∈ ⨆ i : Set.Iio a,
      transfiniteStageField (K := K) e i.1 := by
    rw [← transfiniteStageField_eq_iSup_of_isSuccLimit e a ha]
    exact x.property
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed
    (stageFields_directedBelow e a)] at hx
  exact Set.mem_iUnion.mp hx

theorem residueToLimit_surjective {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) [Nonempty (Set.Iio a)] :
    ∀ x : transfiniteStageField (K := K) e a,
      ∃ (i : Set.Iio a) (y : ringAt P i), residueToLimit P i y = x := by
  intro x
  obtain ⟨i, hxi⟩ := exists_mem_stage_of_limit e a ha x
  obtain ⟨y, hy⟩ := (P.lift i).lift.residue_surjective ⟨x, hxi⟩
  refine ⟨i, y, ?_⟩
  apply Subtype.ext
  exact (residueToLimit_coe P i y).trans (congrArg Subtype.val hy)

/-- The full directed-colimit datum attached to a compatible limit prefix. -/
noncomputable def limitData {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) [Nonempty (Set.Iio a)]
    (i₀ : Set.Iio a) :
    CompleteCharZeroDVRLiftUniformizerLimitData (ringAt P) (ringMap P)
      (ringUniformizer P) (residueToLimit P) i₀ :=
  CompleteCharZeroDVRLiftUniformizerLimitData.ofCompatibleDirectedSystem
    (ringAt P) (ringMap P) (ringUniformizer P) (ringUniformizer_irreducible P)
    (ringUniformizer_maps P) (ringMap_injective P) (residueToLimit P)
    (residueToLimit_compatible P) (residueToLimit_surjective e a ha P) i₀

/-- The actual map from a ring at an earlier stage into the completed ring at
the limit stage. -/
noncomputable def limitInclusion {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) [Nonempty (Set.Iio a)]
    (i₀ i : Set.Iio a) :
    let D := limitData e a ha P i₀
    let _ : CommRing D.target.lift.R := D.target.lift.commRing
    ringAt P i →+* D.target.lift.R := by
  let D := limitData e a ha P i₀
  letI : CommRing D.target.lift.R := D.target.lift.commRing
  exact D.inclusion.comp (DirectLimit.Ring.of (ringAt P) (ringMap P) i)

/-- Each earlier-stage map into the completed limit ring is injective. -/
theorem limitInclusion_injective {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) [Nonempty (Set.Iio a)]
    (i₀ i : Set.Iio a) :
    let D := limitData e a ha P i₀
    let _ : CommRing D.target.lift.R := D.target.lift.commRing
    Function.Injective (limitInclusion e a ha P i₀ i) := by
  let D := limitData e a ha P i₀
  letI : CommRing D.target.lift.R := D.target.lift.commRing
  apply D.inclusion_injective.comp
  exact DirectLimit.mk_injective (ringMap P) (ringMap_injective P) i

/-- The maps into the completed limit ring preserve the chosen uniformizer. -/
theorem limitInclusion_uniformizer {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) [Nonempty (Set.Iio a)]
    (i₀ i : Set.Iio a) :
    let D := limitData e a ha P i₀
    let _ : CommRing D.target.lift.R := D.target.lift.commRing
    limitInclusion e a ha P i₀ i (ringUniformizer P i) = D.target.uniformizer := by
  let D := limitData e a ha P i₀
  letI : CommRing D.target.lift.R := D.target.lift.commRing
  change D.inclusion (DirectLimit.Ring.of (ringAt P) (ringMap P) i
      (ringUniformizer P i)) = D.target.uniformizer
  calc
    D.inclusion (DirectLimit.Ring.of (ringAt P) (ringMap P) i (ringUniformizer P i)) =
        D.inclusion (directLimitUniformizer (ringAt P) (ringMap P) i (ringUniformizer P)) := rfl
    _ = D.inclusion (directLimitUniformizer (ringAt P) (ringMap P) i₀ (ringUniformizer P)) :=
      congrArg D.inclusion (directLimitUniformizer_eq_any (ringAt P) (ringMap P)
        (ringUniformizer P) (ringUniformizer_maps P) i i₀)
    _ = D.target.uniformizer := D.uniformizer_maps

/-- The earlier-stage maps into the completed limit ring retain the prescribed
residue-field maps. -/
theorem limitInclusion_residue {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) [Nonempty (Set.Iio a)]
    (i₀ i : Set.Iio a) (x : ringAt P i) :
    let D := limitData e a ha P i₀
    let _ : CommRing D.target.lift.R := D.target.lift.commRing
    D.target.lift.residue (limitInclusion e a ha P i₀ i x) = residueToLimit P i x := by
  let D := limitData e a ha P i₀
  letI : CommRing D.target.lift.R := D.target.lift.commRing
  change D.target.lift.residue
      (D.inclusion (DirectLimit.Ring.of (ringAt P) (ringMap P) i x)) = residueToLimit P i x
  exact D.residue_commutes i x

/-- An index below the successor of `a` which is not below `a` is precisely
the newly added index. -/
theorem index_eq_of_lt_succ_of_not_lt {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (a : ι) (ha : ¬ IsMax a) (i : Set.Iio (Order.succ a)) (hi : ¬ i.1 < a) :
    i.1 = a := by
  apply le_antisymm
  · exact (Order.lt_succ_iff_of_not_isMax ha).mp i.2
  · exact le_of_not_gt hi

/-- The lift carried at each index after adjoining one successor stage.  The
predecessor prefix is retained verbatim, and the sole new index is assigned
the supplied successor lift. -/
noncomputable def successorPrefixLift {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a)) :
    ∀ i : Set.Iio (Order.succ a),
      CompleteCharZeroDVRLiftWithUniformizer (transfiniteStageField (K := K) e i.1) :=
  fun i => by
    by_cases hi : i.1 < a
    · exact P.lift ⟨i.1, hi⟩
    · have hia := index_eq_of_lt_succ_of_not_lt a ha i hi
      rw [hia]
      exact D

theorem successorPrefixLift_of_lt {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (i : Set.Iio (Order.succ a)) (hi : i.1 < a) :
    successorPrefixLift e a ha P D i = P.lift ⟨i.1, hi⟩ := by
  rw [successorPrefixLift]
  split <;> simp_all

noncomputable def successorIndex {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (a : ι) (ha : ¬ IsMax a) : Set.Iio (Order.succ a) :=
  ⟨a, (Order.lt_succ_iff_of_not_isMax ha).mpr le_rfl⟩

theorem successorPrefixLift_new {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    : successorPrefixLift e a ha P D (successorIndex a ha) = D := by
  rw [successorPrefixLift]
  split
  · rename_i h
    exact (lt_irrefl _ h).elim
  · rfl

/-- Transporting a retained lift along an equality transports its selected
uniformizer to the selected uniformizer. -/
theorem ringEquiv_cast_uniformizer {k : Type u} [Field k]
    (E F : CompleteCharZeroDVRLiftWithUniformizer k) (h : E = F) :
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k, CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    RingEquiv.cast (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k => Q.lift.R) h
      E.uniformizer = F.uniformizer := by
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k, CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  subst F
  rfl

/-- Transporting a retained lift along an equality also commutes with its
residue map. -/
theorem ringEquiv_cast_residue {k : Type u} [Field k]
    (E F : CompleteCharZeroDVRLiftWithUniformizer k) (h : E = F) :
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k, CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    ∀ x : E.lift.R,
      F.lift.residue
        (RingEquiv.cast (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k => Q.lift.R) h x) =
          E.lift.residue x := by
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k, CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  subst F
  intro x
  rfl

/-- The inverse equality transport has the corresponding reverse residue
compatibility. -/
theorem ringEquiv_cast_symm_residue {k : Type u} [Field k]
    (E F : CompleteCharZeroDVRLiftWithUniformizer k) (h : E = F) :
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k, CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    ∀ y : F.lift.R,
      E.lift.residue
        ((RingEquiv.cast (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer k => Q.lift.R) h).symm y) =
          F.lift.residue y := by
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer k, CommRing Q.lift.R :=
    fun Q => Q.lift.commRing
  subst F
  intro y
  rfl

/-- The transition maps after a successor extension.  The three possible
arrows are inherited from the old prefix, supplied by the cocone into the
new stage, or the identity at that new stage. -/
noncomputable def successorPrefixInclusion {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D) :
    ∀ i j (h : i ≤ j),
      letI : CommRing (successorPrefixLift e a ha P D i).lift.R :=
        (successorPrefixLift e a ha P D i).lift.commRing
      letI : CommRing (successorPrefixLift e a ha P D j).lift.R :=
        (successorPrefixLift e a ha P D j).lift.commRing
      (successorPrefixLift e a ha P D i).lift.R →+*
        (successorPrefixLift e a ha P D j).lift.R := by
  intro i j hij
  classical
  by_cases hi : i.1 < a
  · let i' : Set.Iio a := ⟨i.1, hi⟩
    by_cases hj : j.1 < a
    · let j' : Set.Iio a := ⟨j.1, hj⟩
      have hij' : i' ≤ j' := hij
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D i hi)
      let eJ := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e j.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D j hj)
      exact eJ.symm.toRingHom.comp ((P.inclusion i' j' hij').comp eI.toRingHom)
    · have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
      have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
      subst j
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D i hi)
      let eJ := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a) => Q.lift.R)
        (successorPrefixLift_new e a ha P D)
      letI : CommRing (successorPrefixLift e a ha P D (successorIndex a ha)).lift.R :=
        (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
      exact eJ.symm.toRingHom.comp ((C.inclusion i').comp eI.toRingHom)
  · have hieq : i.1 = a := index_eq_of_lt_succ_of_not_lt a ha i hi
    have hi_sub : i = successorIndex a ha := Subtype.ext hieq
    subst i
    by_cases hj : j.1 < a
    · have : False := not_lt_of_ge hij hj
      exact this.elim
    · have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
      have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
      subst j
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a) => Q.lift.R)
        (successorPrefixLift_new e a ha P D)
      letI : CommRing (successorPrefixLift e a ha P D (successorIndex a ha)).lift.R :=
        (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
      exact eI.symm.toRingHom.comp eI.toRingHom

/-- The explicit transported successor maps are injective: the old maps and
the cocone maps are injective, and every transport is a ring equivalence. -/
theorem successorPrefixInclusion_injective {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D)
    (i j : Set.Iio (Order.succ a)) (h : i ≤ j) :
    letI : CommRing (successorPrefixLift e a ha P D i).lift.R :=
      (successorPrefixLift e a ha P D i).lift.commRing
    letI : CommRing (successorPrefixLift e a ha P D j).lift.R :=
      (successorPrefixLift e a ha P D j).lift.commRing
    Function.Injective (successorPrefixInclusion e a ha P D C i j h) := by
  classical
  by_cases hi : i.1 < a
  · let i' : Set.Iio a := ⟨i.1, hi⟩
    by_cases hj : j.1 < a
    · let j' : Set.Iio a := ⟨j.1, hj⟩
      have hij' : i' ≤ j' := h
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D i hi)
      let eJ := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e j.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D j hj)
      unfold successorPrefixInclusion
      simp only [dif_pos hi, dif_pos hj]
      change Function.Injective (eJ.symm.toRingHom.comp
        ((P.inclusion i' j' hij').comp eI.toRingHom))
      exact eJ.symm.injective.comp ((P.inclusion_injective i' j' hij').comp eI.injective)
    · have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
      have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
      subst j
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D i hi)
      let eJ := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a) => Q.lift.R)
        (successorPrefixLift_new e a ha P D)
      letI : CommRing (successorPrefixLift e a ha P D (successorIndex a ha)).lift.R :=
        (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
      unfold successorPrefixInclusion
      simp only [dif_pos hi, dif_neg hj]
      change Function.Injective (eJ.symm.toRingHom.comp ((C.inclusion i').comp eI.toRingHom))
      exact eJ.symm.injective.comp ((C.inclusion_injective i').comp eI.injective)
  · have hieq : i.1 = a := index_eq_of_lt_succ_of_not_lt a ha i hi
    have hi_sub : i = successorIndex a ha := Subtype.ext hieq
    subst i
    by_cases hj : j.1 < a
    · have : False := not_lt_of_ge h hj
      exact this.elim
    · have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
      have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
      subst j
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a) => Q.lift.R)
        (successorPrefixLift_new e a ha P D)
      letI : CommRing (successorPrefixLift e a ha P D (successorIndex a ha)).lift.R :=
        (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
      unfold successorPrefixInclusion
      simp only [dif_neg hi, dif_neg hj]
      change Function.Injective (eI.symm.toRingHom.comp eI.toRingHom)
      exact eI.symm.injective.comp eI.injective

/-- The successor maps carry the selected uniformizer forward. -/
theorem successorPrefixInclusion_uniformizer {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D)
    (i j : Set.Iio (Order.succ a)) (h : i ≤ j) :
    letI : CommRing (successorPrefixLift e a ha P D i).lift.R :=
      (successorPrefixLift e a ha P D i).lift.commRing
    letI : CommRing (successorPrefixLift e a ha P D j).lift.R :=
      (successorPrefixLift e a ha P D j).lift.commRing
    successorPrefixInclusion e a ha P D C i j h
      (successorPrefixLift e a ha P D i).uniformizer =
        (successorPrefixLift e a ha P D j).uniformizer := by
  classical
  by_cases hi : i.1 < a
  · let i' : Set.Iio a := ⟨i.1, hi⟩
    by_cases hj : j.1 < a
    · let j' : Set.Iio a := ⟨j.1, hj⟩
      have hij' : i' ≤ j' := h
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D i hi)
      let eJ := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e j.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D j hj)
      unfold successorPrefixInclusion
      simp only [dif_pos hi, dif_pos hj]
      change eJ.symm (P.inclusion i' j' hij' (eI _)) = _
      have hIu := ringEquiv_cast_uniformizer
        (successorPrefixLift e a ha P D i) (P.lift i')
        (successorPrefixLift_of_lt e a ha P D i hi)
      have hJu := ringEquiv_cast_uniformizer
        (successorPrefixLift e a ha P D j) (P.lift j')
        (successorPrefixLift_of_lt e a ha P D j hj)
      rw [hIu, P.uniformizer_maps i' j' hij']
      apply eJ.injective
      simpa [eJ, j'] using hJu.symm
    · have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
      have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
      subst j
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D i hi)
      let eJ := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a) => Q.lift.R)
        (successorPrefixLift_new e a ha P D)
      letI : CommRing (successorPrefixLift e a ha P D (successorIndex a ha)).lift.R :=
        (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
      unfold successorPrefixInclusion
      simp only [dif_pos hi, dif_neg hj]
      change eJ.symm (C.inclusion i' (eI _)) = _
      have hIu := ringEquiv_cast_uniformizer
        (successorPrefixLift e a ha P D i) (P.lift i')
        (successorPrefixLift_of_lt e a ha P D i hi)
      have hJu := ringEquiv_cast_uniformizer
        (successorPrefixLift e a ha P D (successorIndex a ha)) D
        (successorPrefixLift_new e a ha P D)
      rw [hIu, C.uniformizer_maps i']
      apply eJ.injective
      rw [eJ.apply_symm_apply]
      convert hJu.symm using 1 <;> rfl
  · have hieq : i.1 = a := index_eq_of_lt_succ_of_not_lt a ha i hi
    have hi_sub : i = successorIndex a ha := Subtype.ext hieq
    subst i
    by_cases hj : j.1 < a
    · have : False := not_lt_of_ge h hj
      exact this.elim
    · have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
      have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
      subst j
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a), CommRing Q.lift.R := fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a) => Q.lift.R)
        (successorPrefixLift_new e a ha P D)
      letI : CommRing (successorPrefixLift e a ha P D (successorIndex a ha)).lift.R :=
        (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
      unfold successorPrefixInclusion
      simp only [dif_neg hi, dif_neg hj]
      change eI.symm (eI _) = _
      exact eI.symm_apply_apply _

/-- Residue compatibility for a successor-prefix map whose source and target
both belong to the old prefix. -/
theorem successorPrefixInclusion_residue_of_lt {ι : Type u}
    [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D)
    (i j : Set.Iio (Order.succ a)) (h : i ≤ j)
    (hi : i.1 < a) (hj : j.1 < a)
    (x : (successorPrefixLift e a ha P D i).lift.R) :
    letI : CommRing (successorPrefixLift e a ha P D i).lift.R :=
      (successorPrefixLift e a ha P D i).lift.commRing
    letI : CommRing (successorPrefixLift e a ha P D j).lift.R :=
      (successorPrefixLift e a ha P D j).lift.commRing
    (successorPrefixLift e a ha P D j).lift.residue
        (successorPrefixInclusion e a ha P D C i j h x) =
      transfiniteStageFieldInclusion (K := K) e h
        ((successorPrefixLift e a ha P D i).lift.residue x) := by
  let i' : Set.Iio a := ⟨i.1, hi⟩
  let j' : Set.Iio a := ⟨j.1, hj⟩
  have hij' : i' ≤ j' := h
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
  let hI := successorPrefixLift_of_lt e a ha P D i hi
  let hJ := successorPrefixLift_of_lt e a ha P D j hj
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R) hI
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e j.1) => Q.lift.R) hJ
  unfold successorPrefixInclusion
  simp only [dif_pos hi, dif_pos hj]
  change (successorPrefixLift e a ha P D j).lift.residue
    (eJ.symm (P.inclusion i' j' hij' (eI x))) = _
  rw [ringEquiv_cast_symm_residue _ _ hJ]
  rw [P.residue_commutes i' j' hij']
  rw [ringEquiv_cast_residue _ _ hI]

/-- Residue compatibility for the map from an old prefix stage to the newly
adjoined successor stage. -/
theorem successorPrefixInclusion_residue_to_new {ι : Type u}
    [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D)
    (i j : Set.Iio (Order.succ a)) (h : i ≤ j)
    (hi : i.1 < a) (hj : ¬ j.1 < a)
    (x : (successorPrefixLift e a ha P D i).lift.R) :
    letI : CommRing (successorPrefixLift e a ha P D i).lift.R :=
      (successorPrefixLift e a ha P D i).lift.commRing
    letI : CommRing (successorPrefixLift e a ha P D j).lift.R :=
      (successorPrefixLift e a ha P D j).lift.commRing
    (successorPrefixLift e a ha P D j).lift.residue
        (successorPrefixInclusion e a ha P D C i j h x) =
      transfiniteStageFieldInclusion (K := K) e h
        ((successorPrefixLift e a ha P D i).lift.residue x) := by
  have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
  have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
  subst j
  let i' : Set.Iio a := ⟨i.1, hi⟩
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R := fun Q => Q.lift.commRing
  letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a), CommRing Q.lift.R := fun Q => Q.lift.commRing
  let hI := successorPrefixLift_of_lt e a ha P D i hi
  let hJ := successorPrefixLift_new e a ha P D
  let eI := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e i.1) => Q.lift.R) hI
  let eJ := RingEquiv.cast
    (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a) => Q.lift.R) hJ
  letI : CommRing (successorPrefixLift e a ha P D (successorIndex a ha)).lift.R :=
    (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
  unfold successorPrefixInclusion
  simp only [dif_pos hi, dif_neg hj]
  change (successorPrefixLift e a ha P D (successorIndex a ha)).lift.residue
    (eJ.symm (C.inclusion i' (eI x))) = _
  have hresJ := ringEquiv_cast_symm_residue
    (successorPrefixLift e a ha P D (successorIndex a ha)) D hJ
      (C.inclusion i' (eI x))
  have hresI := ringEquiv_cast_residue
    (successorPrefixLift e a ha P D i) (P.lift i') hI x
  have hmain :
      (successorPrefixLift e a ha P D (successorIndex a ha)).lift.residue
          (eJ.symm (C.inclusion i' (eI x))) =
        transfiniteStageFieldInclusion (K := K) e i'.2.le
          ((successorPrefixLift e a ha P D i).lift.residue x) := by
    calc
      _ = D.lift.residue (C.inclusion i' (eI x)) := by
        convert hresJ using 1 <;> rfl
      _ = transfiniteStageFieldInclusion (K := K) e i'.2.le
          ((P.lift i').lift.residue (eI x)) := C.residue_commutes i' (eI x)
      _ = transfiniteStageFieldInclusion (K := K) e i'.2.le
          ((successorPrefixLift e a ha P D i).lift.residue x) := by
        rw [hresI]
  convert hmain using 1 <;> rfl

/-- Every transition map in the extended successor prefix induces the
canonical inclusion on residue fields. -/
theorem successorPrefixInclusion_residue {ι : Type u}
    [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D)
    (i j : Set.Iio (Order.succ a)) (h : i ≤ j)
    (x : (successorPrefixLift e a ha P D i).lift.R) :
    letI : CommRing (successorPrefixLift e a ha P D i).lift.R :=
      (successorPrefixLift e a ha P D i).lift.commRing
    letI : CommRing (successorPrefixLift e a ha P D j).lift.R :=
      (successorPrefixLift e a ha P D j).lift.commRing
    (successorPrefixLift e a ha P D j).lift.residue
        (successorPrefixInclusion e a ha P D C i j h x) =
      transfiniteStageFieldInclusion (K := K) e h
        ((successorPrefixLift e a ha P D i).lift.residue x) := by
  classical
  by_cases hi : i.1 < a
  · by_cases hj : j.1 < a
    · exact successorPrefixInclusion_residue_of_lt e a ha P D C i j h hi hj x
    · exact successorPrefixInclusion_residue_to_new e a ha P D C i j h hi hj x
  · have hieq : i.1 = a := index_eq_of_lt_succ_of_not_lt a ha i hi
    have hi_sub : i = successorIndex a ha := Subtype.ext hieq
    subst i
    by_cases hj : j.1 < a
    · exact (hi (lt_of_le_of_lt h hj)).elim
    · have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
      have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
      subst j
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a), CommRing Q.lift.R :=
        fun Q => Q.lift.commRing
      let hI := successorPrefixLift_new e a ha P D
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a) => Q.lift.R) hI
      letI : CommRing (successorPrefixLift e a ha P D
          (successorIndex a ha)).lift.R :=
        (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
      unfold successorPrefixInclusion
      simp only [dif_neg hi, dif_neg hj]
      change (successorPrefixLift e a ha P D (successorIndex a ha)).lift.residue
          (eI.symm (eI x)) = _
      rw [eI.symm_apply_apply]
      apply Subtype.ext
      rfl

/-- A successor-prefix transition map from a stage to itself is the identity. -/
theorem successorPrefixInclusion_self {ι : Type u}
    [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D)
    (i : Set.Iio (Order.succ a)) :
    letI : CommRing (successorPrefixLift e a ha P D i).lift.R :=
      (successorPrefixLift e a ha P D i).lift.commRing
    successorPrefixInclusion e a ha P D C i i le_rfl =
      RingHom.id (successorPrefixLift e a ha P D i).lift.R := by
  classical
  by_cases hi : i.1 < a
  · let i' : Set.Iio a := ⟨i.1, hi⟩
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
        (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    let eI := RingEquiv.cast
      (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
        (transfiniteStageField (K := K) e i.1) => Q.lift.R)
      (successorPrefixLift_of_lt e a ha P D i hi)
    unfold successorPrefixInclusion
    simp only [dif_pos hi]
    change eI.symm.toRingHom.comp
        ((P.inclusion i' i' le_rfl).comp eI.toRingHom) = RingHom.id _
    rw [P.inclusion_self]
    ext x
    exact eI.symm_apply_apply x
  · have hieq : i.1 = a := index_eq_of_lt_succ_of_not_lt a ha i hi
    have hi_sub : i = successorIndex a ha := Subtype.ext hieq
    subst i
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
        (transfiniteStageField (K := K) e a), CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    let eI := RingEquiv.cast
      (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
        (transfiniteStageField (K := K) e a) => Q.lift.R)
      (successorPrefixLift_new e a ha P D)
    letI : CommRing (successorPrefixLift e a ha P D
        (successorIndex a ha)).lift.R :=
      (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
    unfold successorPrefixInclusion
    simp only [dif_neg hi]
    change eI.symm.toRingHom.comp eI.toRingHom = RingHom.id _
    ext x
    exact eI.symm_apply_apply x

/-- Successor-prefix transition maps compose coherently. -/
theorem successorPrefixInclusion_comp {ι : Type u}
    [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D)
    (i j k : Set.Iio (Order.succ a)) (hij : i ≤ j) (hjk : j ≤ k) :
    letI : CommRing (successorPrefixLift e a ha P D i).lift.R :=
      (successorPrefixLift e a ha P D i).lift.commRing
    letI : CommRing (successorPrefixLift e a ha P D j).lift.R :=
      (successorPrefixLift e a ha P D j).lift.commRing
    letI : CommRing (successorPrefixLift e a ha P D k).lift.R :=
      (successorPrefixLift e a ha P D k).lift.commRing
    (successorPrefixInclusion e a ha P D C j k hjk).comp
        (successorPrefixInclusion e a ha P D C i j hij) =
      successorPrefixInclusion e a ha P D C i k (hij.trans hjk) := by
  classical
  by_cases hi : i.1 < a
  · let i' : Set.Iio a := ⟨i.1, hi⟩
    by_cases hj : j.1 < a
    · let j' : Set.Iio a := ⟨j.1, hj⟩
      have hij' : i' ≤ j' := hij
      by_cases hk : k.1 < a
      · let k' : Set.Iio a := ⟨k.1, hk⟩
        have hjk' : j' ≤ k' := hjk
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
          (successorPrefixLift_of_lt e a ha P D i hi)
        let eJ := RingEquiv.cast
          (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
            (transfiniteStageField (K := K) e j.1) => Q.lift.R)
          (successorPrefixLift_of_lt e a ha P D j hj)
        let eK := RingEquiv.cast
          (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
            (transfiniteStageField (K := K) e k.1) => Q.lift.R)
          (successorPrefixLift_of_lt e a ha P D k hk)
        unfold successorPrefixInclusion
        simp only [dif_pos hi, dif_pos hj, dif_pos hk]
        ext x
        change eK.symm (P.inclusion j' k' hjk'
            (eJ (eJ.symm (P.inclusion i' j' hij' (eI x))))) =
          eK.symm (P.inclusion i' k' (hij'.trans hjk') (eI x))
        rw [eJ.apply_symm_apply]
        exact congrArg eK.symm (by
          simpa only [RingHom.comp_apply] using
            congrArg (fun f => f (eI x))
              (P.inclusion_comp i' j' k' hij' hjk'))
      · have hkeq : k.1 = a := index_eq_of_lt_succ_of_not_lt a ha k hk
        have hk_sub : k = successorIndex a ha := Subtype.ext hkeq
        subst k
        letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
            (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
          fun Q => Q.lift.commRing
        letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
            (transfiniteStageField (K := K) e j.1), CommRing Q.lift.R :=
          fun Q => Q.lift.commRing
        letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
            (transfiniteStageField (K := K) e a), CommRing Q.lift.R :=
          fun Q => Q.lift.commRing
        let eI := RingEquiv.cast
          (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
            (transfiniteStageField (K := K) e i.1) => Q.lift.R)
          (successorPrefixLift_of_lt e a ha P D i hi)
        let eJ := RingEquiv.cast
          (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
            (transfiniteStageField (K := K) e j.1) => Q.lift.R)
          (successorPrefixLift_of_lt e a ha P D j hj)
        let eK := RingEquiv.cast
          (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
            (transfiniteStageField (K := K) e a) => Q.lift.R)
          (successorPrefixLift_new e a ha P D)
        letI : CommRing (successorPrefixLift e a ha P D
            (successorIndex a ha)).lift.R :=
          (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
        unfold successorPrefixInclusion
        simp only [dif_pos hi, dif_pos hj, dif_neg hk]
        ext x
        change eK.symm (C.inclusion j'
            (eJ (eJ.symm (P.inclusion i' j' hij' (eI x))))) =
          eK.symm (C.inclusion i' (eI x))
        rw [eJ.apply_symm_apply]
        exact congrArg eK.symm (C.inclusion_comp i' j' hij' (eI x))
    · have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
      have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
      subst j
      have hk : ¬ k.1 < a := fun hk => hj (lt_of_le_of_lt hjk hk)
      have hkeq : k.1 = a := index_eq_of_lt_succ_of_not_lt a ha k hk
      have hk_sub : k = successorIndex a ha := Subtype.ext hkeq
      subst k
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1), CommRing Q.lift.R :=
        fun Q => Q.lift.commRing
      letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a), CommRing Q.lift.R :=
        fun Q => Q.lift.commRing
      let eI := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e i.1) => Q.lift.R)
        (successorPrefixLift_of_lt e a ha P D i hi)
      let eN := RingEquiv.cast
        (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
          (transfiniteStageField (K := K) e a) => Q.lift.R)
        (successorPrefixLift_new e a ha P D)
      letI : CommRing (successorPrefixLift e a ha P D
          (successorIndex a ha)).lift.R :=
        (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
      unfold successorPrefixInclusion
      simp only [dif_pos hi, dif_neg hj, dif_neg hk]
      ext x
      change eN.symm (eN (eN.symm (C.inclusion i' (eI x)))) =
        eN.symm (C.inclusion i' (eI x))
      rw [eN.apply_symm_apply]
  · have hieq : i.1 = a := index_eq_of_lt_succ_of_not_lt a ha i hi
    have hi_sub : i = successorIndex a ha := Subtype.ext hieq
    subst i
    have hj : ¬ j.1 < a := fun hj => hi (lt_of_le_of_lt hij hj)
    have hjeq : j.1 = a := index_eq_of_lt_succ_of_not_lt a ha j hj
    have hj_sub : j = successorIndex a ha := Subtype.ext hjeq
    subst j
    have hk : ¬ k.1 < a := fun hk => hj (lt_of_le_of_lt hjk hk)
    have hkeq : k.1 = a := index_eq_of_lt_succ_of_not_lt a ha k hk
    have hk_sub : k = successorIndex a ha := Subtype.ext hkeq
    subst k
    letI : ∀ Q : CompleteCharZeroDVRLiftWithUniformizer
        (transfiniteStageField (K := K) e a), CommRing Q.lift.R :=
      fun Q => Q.lift.commRing
    let eN := RingEquiv.cast
      (R := fun Q : CompleteCharZeroDVRLiftWithUniformizer
        (transfiniteStageField (K := K) e a) => Q.lift.R)
      (successorPrefixLift_new e a ha P D)
    letI : CommRing (successorPrefixLift e a ha P D
        (successorIndex a ha)).lift.R :=
      (successorPrefixLift e a ha P D (successorIndex a ha)).lift.commRing
    unfold successorPrefixInclusion
    simp only [dif_neg hi, dif_neg hj, dif_neg hk]
    ext x
    change eN.symm (eN (eN.symm (eN x))) = eN.symm (eN x)
    rw [eN.apply_symm_apply]

/-- Extend a compatible retained prefix through one successor stage. -/
noncomputable def successorPrefix {ι : Type u}
    [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D) :
    TransfiniteDVRLiftPrefix (K := K) e (Order.succ a) := {
  lift := successorPrefixLift e a ha P D
  inclusion := successorPrefixInclusion e a ha P D C
  inclusion_injective := successorPrefixInclusion_injective e a ha P D C
  inclusion_self := successorPrefixInclusion_self e a ha P D C
  inclusion_comp := successorPrefixInclusion_comp e a ha P D C
  residue_commutes := successorPrefixInclusion_residue e a ha P D C
  uniformizer_maps := successorPrefixInclusion_uniformizer e a ha P D C
}

/-- Extending a prefix through one successor and restricting back to the old
endpoint recovers the original prefix exactly. -/
theorem restrict_successorPrefix {ι : Type u}
    [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D) :
    restrict (successorPrefix e a ha P D C) a (Order.le_succ a) = P := by
  classical
  apply ext_pointwise
  · intro i
    change (if hi : i.1 < a then P.lift ⟨i.1, hi⟩ else _) = P.lift i
    split
    · congr
    · rename_i h
      exact (h i.2).elim
  · intro i j hij
    let iS : Set.Iio (Order.succ a) :=
      ⟨i.1, i.2.trans_le (Order.le_succ a)⟩
    let jS : Set.Iio (Order.succ a) :=
      ⟨j.1, j.2.trans_le (Order.le_succ a)⟩
    have hiS : iS.1 < a := i.2
    have hjS : jS.1 < a := j.2
    change HEq (successorPrefixInclusion e a ha P D C iS jS hij)
      (P.inclusion i j hij)
    unfold successorPrefixInclusion
    simp only [dif_pos hiS, dif_pos hjS]
    exact transportedRingHom_heq
      (successorPrefixLift e a ha P D iS)
      (P.lift i)
      (successorPrefixLift e a ha P D jS)
      (P.lift j)
      (successorPrefixLift_of_lt e a ha P D iS hiS)
      (successorPrefixLift_of_lt e a ha P D jS hjS)
      (P.inclusion i j hij)

/-- The finite extension datum from the last stage of a successor-indexed
prefix to its endpoint. -/
noncomputable def successorStageExtension {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e (Order.succ a)) :
    let E := transfiniteStageField (K := K) e (successorIndex a ha).1
    let F := transfiniteStageField (K := K) e (Order.succ a)
    let _ : Algebra E F :=
      (IntermediateField.inclusion
        (transfiniteStageField_mono e (Order.le_succ a))).toRingHom.toAlgebra
    CompleteCharZeroDVRLiftUniformizerExtensionData (L := F)
      (P.lift (successorIndex a ha)) := by
  dsimp only
  letI : Algebra (transfiniteStageField (K := K) e (successorIndex a ha).1)
      (transfiniteStageField (K := K) e (Order.succ a)) :=
    (IntermediateField.inclusion
      (transfiniteStageField_mono e (Order.le_succ a))).toRingHom.toAlgebra
  exact transfiniteStageLiftSuccessor e a ha (P.lift (successorIndex a ha))

/-- A prefix ending at a successor has a canonical cocone into the finite
extension lift of its last retained stage. -/
noncomputable def successorStageCocone {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e (Order.succ a)) :
    let Efield := transfiniteStageField (K := K) e (successorIndex a ha).1
    let F := transfiniteStageField (K := K) e (Order.succ a)
    let _ : Algebra Efield F :=
      (IntermediateField.inclusion
        (transfiniteStageField_mono e (Order.le_succ a))).toRingHom.toAlgebra
    TransfiniteDVRLiftCocone e (Order.succ a) P
      (successorStageExtension e a ha P).target := by
  dsimp only
  letI : Algebra (transfiniteStageField (K := K) e (successorIndex a ha).1)
      (transfiniteStageField (K := K) e (Order.succ a)) :=
    (IntermediateField.inclusion
      (transfiniteStageField_mono e (Order.le_succ a))).toRingHom.toAlgebra
  let m := successorIndex a ha
  let E := successorStageExtension e a ha P
  let hlast : ∀ i : Set.Iio (Order.succ a), i ≤ m := fun i =>
    (Order.lt_succ_iff_of_not_isMax ha).mp i.2
  refine {
    inclusion := fun i => E.inclusion.comp (P.inclusion i m (hlast i))
    inclusion_injective := fun i =>
      E.inclusion_injective.comp (P.inclusion_injective i m (hlast i))
    inclusion_comp := ?_
    residue_commutes := ?_
    uniformizer_maps := ?_
  }
  · intro i j hij x
    change E.inclusion (P.inclusion j m (hlast j) (P.inclusion i j hij x)) =
      E.inclusion (P.inclusion i m (hlast i) x)
    exact congrArg E.inclusion (by
      simpa only [RingHom.comp_apply] using
        congrArg (fun f => f x) (P.inclusion_comp i j m hij (hlast j)))
  · intro i x
    change E.target.lift.residue
        (E.inclusion (P.inclusion i m (hlast i) x)) = _
    rw [E.residue_commutes, P.residue_commutes]
    apply Subtype.ext
    rfl
  · intro i
    change E.inclusion (P.inclusion i m (hlast i) (P.lift i).uniformizer) =
      E.target.uniformizer
    rw [P.uniformizer_maps, E.uniformizer_maps]

/-- Completing a compatible prefix at a limit ordinal produces a retained
complete characteristic-zero DVR lift of the corresponding limit field. -/
noncomputable def limitLift {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    CompleteCharZeroDVRLiftWithUniformizer (transfiniteStageField (K := K) e a) := by
  letI : Nonempty (Set.Iio a) := ha.nonempty_Iio.to_subtype
  exact (limitData e a ha P (Classical.choice ha.nonempty_Iio.to_subtype)).target

/-- The maps supplied by a completed directed prefix form a compatible
cocone.  This packages the limit case in exactly the form required when a
transfinite prefix is extended by one more stage. -/
noncomputable def limitCocone {ι : Type u} [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    TransfiniteDVRLiftCocone e a P (limitLift e a ha P) := by
  letI : Nonempty (Set.Iio a) := ha.nonempty_Iio.to_subtype
  let i₀ : Set.Iio a := Classical.choice ha.nonempty_Iio.to_subtype
  let D := limitData e a ha P i₀
  letI : CommRing D.target.lift.R := D.target.lift.commRing
  refine {
    inclusion := fun i => limitInclusion e a ha P i₀ i
    inclusion_injective := fun i => limitInclusion_injective e a ha P i₀ i
    inclusion_comp := ?_
    residue_commutes := fun i x => limitInclusion_residue e a ha P i₀ i x
    uniformizer_maps := fun i => limitInclusion_uniformizer e a ha P i₀ i
  }
  intro i j hij x
  change D.inclusion (DirectLimit.Ring.of (ringAt P) (ringMap P) j
      (P.inclusion i j hij x)) =
    D.inclusion (DirectLimit.Ring.of (ringAt P) (ringMap P) i x)
  change D.inclusion (DirectLimit.Ring.of (ringAt P) (ringMap P) j
      (ringMap P i j hij x)) =
    D.inclusion (DirectLimit.Ring.of (ringAt P) (ringMap P) i x)
  exact congrArg D.inclusion
    (DirectLimit.Ring.of_f (G := ringAt P) (f := ringMap P) hij x)

/-- At a minimal index the base lift is the endpoint lift; there are no
earlier stages from which maps must be supplied. -/
noncomputable def minStageData {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (ha : IsMin a)
    (hK : HasCompleteCharZeroDVRLift K)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    TransfiniteDVRLiftStageData e a P := by
  let D := transfiniteStageLiftMin e a ha hK
  refine {
    lift := D
    cocone := {
      inclusion := fun i => (ha.not_lt i.2).elim
      inclusion_injective := fun i => (ha.not_lt i.2).elim
      inclusion_comp := fun i => (ha.not_lt i.2).elim
      residue_commutes := fun i => (ha.not_lt i.2).elim
      uniformizer_maps := fun i => (ha.not_lt i.2).elim
    }
  }

/-- At a successor endpoint, extend the last retained lift through the finite
residue-field extension and compose all earlier transition maps with it. -/
noncomputable def successorStageData {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e (Order.succ a)) :
    TransfiniteDVRLiftStageData e (Order.succ a) P := by
  letI : Algebra (transfiniteStageField (K := K) e (successorIndex a ha).1)
      (transfiniteStageField (K := K) e (Order.succ a)) :=
    (IntermediateField.inclusion
      (transfiniteStageField_mono e (Order.le_succ a))).toRingHom.toAlgebra
  exact {
    lift := (successorStageExtension e a ha P).target
    cocone := successorStageCocone e a ha P
  }

/-- At a limit endpoint, the directed colimit and completion already
constructed above supply the endpoint lift and its compatible cocone. -/
noncomputable def limitStageData {ι : Type u}
    [LinearOrder ι] [SuccOrder ι]
    (e : ι → L) (a : ι) (ha : Order.IsSuccLimit a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    TransfiniteDVRLiftStageData e a P := {
  lift := limitLift e a ha P
  cocone := limitCocone e a ha P
}

/-- Uniformly construct the lift and compatible cocone at the endpoint of
any retained prefix, dispatching to the minimal, successor, or limit case. -/
noncomputable def stageData {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (hK : HasCompleteCharZeroDVRLift K) (a : ι) :
    ∀ P : TransfiniteDVRLiftPrefix (K := K) e a,
      TransfiniteDVRLiftStageData e a P :=
  Order.isSuccLimitRecOn
    (motive := fun b => ∀ P : TransfiniteDVRLiftPrefix (K := K) e b,
      TransfiniteDVRLiftStageData e b P)
    a
    (fun b hb P => minStageData e b hb hK P)
    (fun b hb P => successorStageData e b hb P)
    (fun b hb P => limitStageData e b hb P)

/-- Extend any retained prefix by one stage, using the endpoint datum selected
by the minimal/successor/limit recursion. -/
noncomputable def extendPrefix {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (hK : HasCompleteCharZeroDVRLift K)
    (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) :
    TransfiniteDVRLiftPrefix (K := K) e (Order.succ a) :=
  successorPrefix e a ha P (stageData e hK a P).lift
    (stageData e hK a P).cocone

end AllCharacteristics.TransfiniteDVRLiftPrefix
