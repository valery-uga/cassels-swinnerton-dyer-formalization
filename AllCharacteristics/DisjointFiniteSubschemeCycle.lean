import AllCharacteristics.ClosedImmersionCyclePushforward
import PfaffianDescent.IntrinsicFiniteCycle
import Mathlib.AlgebraicGeometry.Limits

/-!
# Fundamental cycles of disjoint finite schemes

The intrinsic fundamental cycle of a disjoint union is the sum of the
fundamental cycles of its two components.  This keeps the local lengths of
nonreduced finite subschemes while allowing the corresponding ambient cycles
to be added.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u

/-- Each component of a binary coproduct of schemes is also a closed
immersion. -/
theorem isClosedImmersion_coprod_inl {U V : Scheme.{u}} :
    IsClosedImmersion (coprod.inl : U ⟶ U ⨿ V) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hrange : Set.range (coprod.inl : U ⟶ U ⨿ V) =
      (coprodMk U V) '' Set.range (Sum.inl : U → U ⊕ V) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Sum.inl y, by simp⟩
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, by simp⟩
  rw [hrange]
  exact (coprodMk U V).isClosedMap _ isClosed_range_inl

/-- Each component of a binary coproduct of schemes is also a closed
immersion. -/
theorem isClosedImmersion_coprod_inr {U V : Scheme.{u}} :
    IsClosedImmersion (coprod.inr : V ⟶ U ⨿ V) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hrange : Set.range (coprod.inr : V ⟶ U ⨿ V) =
      (coprodMk U V) '' Set.range (Sum.inr : V → U ⊕ V) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Sum.inr y, by simp⟩
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, by simp⟩
  rw [hrange]
  exact (coprodMk U V).isClosedMap _ isClosed_range_inr

/-- The local-length fundamental cycle of an Artinian coproduct is the sum
of the closed-immersion pushforwards of its two component cycles. -/
theorem fundamentalZeroCycle_coprod
    {U V : Scheme.{u}} [IsArtinianScheme U] [IsArtinianScheme V]
    [IsArtinianScheme (U ⨿ V)] :
    letI : IsClosedImmersion (coprod.inl : U ⟶ U ⨿ V) :=
      isClosedImmersion_coprod_inl
    letI : IsClosedImmersion (coprod.inr : V ⟶ U ⨿ V) :=
      isClosedImmersion_coprod_inr
    fundamentalZeroCycle (U ⨿ V) =
      pushforwardClosedCycle (coprod.inl : U ⟶ U ⨿ V) (fundamentalZeroCycle U) +
      pushforwardClosedCycle (coprod.inr : V ⟶ U ⨿ V) (fundamentalZeroCycle V) := by
  letI : IsClosedImmersion (coprod.inl : U ⟶ U ⨿ V) :=
    isClosedImmersion_coprod_inl
  letI : IsClosedImmersion (coprod.inr : V ⟶ U ⨿ V) :=
    isClosedImmersion_coprod_inr
  have hinl : Function.Injective (closedPointMap (coprod.inl : U ⟶ U ⨿ V)) := by
    intro x y hxy
    apply Subtype.ext
    exact (IsOpenImmersion.iff_isIso_stalkMap.mp
      (inferInstance : IsOpenImmersion (coprod.inl : U ⟶ U ⨿ V))).1.injective
      (congrArg Subtype.val hxy)
  have hinr : Function.Injective (closedPointMap (coprod.inr : V ⟶ U ⨿ V)) := by
    intro x y hxy
    apply Subtype.ext
    exact (IsOpenImmersion.iff_isIso_stalkMap.mp
      (inferInstance : IsOpenImmersion (coprod.inr : V ⟶ U ⨿ V))).1.injective
      (congrArg Subtype.val hxy)
  apply Finsupp.ext
  intro x
  generalize hy : (coprodMk U V).symm x.1 = y
  rcases y with u | v
  · let ux : closedPoints U := ⟨u, isClosed_singleton⟩
    have hval : (coprod.inl : U ⟶ U ⨿ V) u = x.1 := by
      have h := congrArg (coprodMk U V) hy
      rw [Homeomorph.apply_symm_apply, coprodMk_inl] at h
      exact h.symm
    have hx : x = closedPointMap (coprod.inl : U ⟶ U ⨿ V) ux := by
      apply Subtype.ext
      change x.1 = (coprod.inl : U ⟶ U ⨿ V) ux.1
      exact hval.symm
    rw [hx]
    change (fundamentalZeroCycle (U ⨿ V)) _ =
      (fundamentalZeroCycle U).mapDomain (closedPointMap (coprod.inl : U ⟶ U ⨿ V)) _ +
      (fundamentalZeroCycle V).mapDomain (closedPointMap (coprod.inr : V ⟶ U ⨿ V)) _
    rw [Finsupp.mapDomain_apply hinl]
    have hnot : closedPointMap (coprod.inl : U ⟶ U ⨿ V) ux ∉
        Set.range (closedPointMap (coprod.inr : V ⟶ U ⨿ V)) := by
      rintro ⟨v, hv⟩
      have hval := congrArg Subtype.val hv
      exact inl_ne_inr U V ux.1 v.1 hval.symm
    rw [Finsupp.mapDomain_of_notMem_range _ _ hnot, add_zero]
    change (Module.length ((U ⨿ V).presheaf.stalk ((coprod.inl : U ⟶ U ⨿ V) ux.1))
      ((U ⨿ V).presheaf.stalk ((coprod.inl : U ⟶ U ⨿ V) ux.1))).toNat = _
    exact congrArg ENat.toNat (ring_length_eq_of_ringEquiv
      (asIso ((coprod.inl : U ⟶ U ⨿ V).stalkMap ux.1)).commRingCatIsoToRingEquiv)
  · let vx : closedPoints V := ⟨v, isClosed_singleton⟩
    have hval : (coprod.inr : V ⟶ U ⨿ V) v = x.1 := by
      have h := congrArg (coprodMk U V) hy
      rw [Homeomorph.apply_symm_apply, coprodMk_inr] at h
      exact h.symm
    have hx : x = closedPointMap (coprod.inr : V ⟶ U ⨿ V) vx := by
      apply Subtype.ext
      change x.1 = (coprod.inr : V ⟶ U ⨿ V) vx.1
      exact hval.symm
    rw [hx]
    change (fundamentalZeroCycle (U ⨿ V)) _ =
      (fundamentalZeroCycle U).mapDomain (closedPointMap (coprod.inl : U ⟶ U ⨿ V)) _ +
      (fundamentalZeroCycle V).mapDomain (closedPointMap (coprod.inr : V ⟶ U ⨿ V)) _
    rw [Finsupp.mapDomain_apply hinr]
    have hnot : closedPointMap (coprod.inr : V ⟶ U ⨿ V) vx ∉
        Set.range (closedPointMap (coprod.inl : U ⟶ U ⨿ V)) := by
      rintro ⟨u, hu⟩
      have hval := congrArg Subtype.val hu
      exact inl_ne_inr U V u.1 vx.1 hval
    rw [Finsupp.mapDomain_of_notMem_range _ _ hnot, zero_add]
    change (Module.length ((U ⨿ V).presheaf.stalk ((coprod.inr : V ⟶ U ⨿ V) vx.1))
      ((U ⨿ V).presheaf.stalk ((coprod.inr : V ⟶ U ⨿ V) vx.1))).toNat = _
    exact congrArg ENat.toNat (ring_length_eq_of_ringEquiv
      (asIso ((coprod.inr : V ⟶ U ⨿ V).stalkMap vx.1)).commRingCatIsoToRingEquiv)

/-- Rewriting the preceding formula through residue-weighted proper
pushforward gives the cycle decomposition used by finite intersections. -/
theorem fundamentalZeroCycle_coprod_pushforward
    {U V : Scheme.{u}} [IsArtinianScheme U] [IsArtinianScheme V]
    [IsArtinianScheme (U ⨿ V)] :
    letI : IsClosedImmersion (coprod.inl : U ⟶ U ⨿ V) :=
      isClosedImmersion_coprod_inl
    letI : IsClosedImmersion (coprod.inr : V ⟶ U ⨿ V) :=
      isClosedImmersion_coprod_inr
    fundamentalZeroCycle (U ⨿ V) =
      pushforwardCycle (coprod.inl : U ⟶ U ⨿ V) (fundamentalZeroCycle U) +
      pushforwardCycle (coprod.inr : V ⟶ U ⨿ V) (fundamentalZeroCycle V) := by
  letI : IsClosedImmersion (coprod.inl : U ⟶ U ⨿ V) :=
    isClosedImmersion_coprod_inl
  letI : IsClosedImmersion (coprod.inr : V ⟶ U ⨿ V) :=
    isClosedImmersion_coprod_inr
  rw [fundamentalZeroCycle_coprod]
  simp only [← pushforwardCycle_eq_pushforwardClosedCycle]

end AllCharacteristics
