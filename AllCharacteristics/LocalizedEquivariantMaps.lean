import AllCharacteristics.LocalizedGroupAction

/-!
# Equivariance of the actual localization maps

Equivariant coefficient maps remain equivariant after localization whenever
the localized actions extend the original ones. In particular this applies
to the canonically constructed actions at invariant denominators.
-/

namespace AllCharacteristics
universe u v
section General
variable (A B L M : Type u) [CommRing A] [CommRing B] [CommRing L] [CommRing M]
variable [Algebra A L] [Algebra B M]
variable (G : Type v) [Group G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [MulSemiringAction G L] [MulSemiringAction G M]
variable [SMulDistribClass G A L] [SMulDistribClass G B M]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)
variable (t : A) [IsLocalization.Away t L] [IsLocalization.Away (φ t) M]

/-- The actual localized map acts on original coefficients by the original ring homomorphism. -/
theorem localizedRingMap_algebraMap (a : A) :
    IsLocalization.Away.map L M φ t (algebraMap A L a) = algebraMap B M (φ a) := by
  have hmap : Submonoid.powers t ≤ (Submonoid.powers (φ t)).comap φ := by
    rintro z ⟨m, rfl⟩
    exact ⟨m, (map_pow φ t m).symm⟩
  exact IsLocalization.map_eq (S := L) (Q := M) (g := φ)
    (M := Submonoid.powers t) (T := Submonoid.powers (φ t)) hmap a

include hφ in
/-- Compatible group actions make the actual localization map equivariant. -/
theorem localizedRingMap_equivariant (g : G) (z : L) :
    IsLocalization.Away.map L M φ t (g • z) = g • IsLocalization.Away.map L M φ t z := by
  have he : (IsLocalization.Away.map L M φ t).comp (MulSemiringAction.toRingHom G L g) =
      (MulSemiringAction.toRingHom G M g).comp (IsLocalization.Away.map L M φ t) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    apply RingHom.ext
    intro a
    change IsLocalization.Away.map L M φ t (g • algebraMap A L a) =
      g • IsLocalization.Away.map L M φ t (algebraMap A L a)
    rw [← algebraMap.coe_smul' g a L, localizedRingMap_algebraMap,
      localizedRingMap_algebraMap, ← algebraMap.coe_smul' g (φ a) M, hφ]
  exact congrArg (fun h : L →+* M ↦ h z) he

end General

section Canonical
variable (A B : Type u) [CommRing A] [CommRing B]
variable (G : Type v) [Group G] [MulSemiringAction G A] [MulSemiringAction G B]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)
variable (t : A) (ht : ∀ g : G, g • t = t)

/-- The actual canonical localization map is equivariant for the constructed localization actions. -/
theorem canonicalAwayMap_equivariant :
    let htB : ∀ g : G, g • φ t = φ t := fun g ↦ by rw [← hφ, ht]
    letI := localizedGroupAction A (Localization.Away t) G t ht
    letI := localizedGroupAction B (Localization.Away (φ t)) G (φ t) htB
    ∀ (g : G) (z : Localization.Away t),
      Localization.awayMap φ t (g • z) = g • Localization.awayMap φ t z := by
  let htB : ∀ g : G, g • φ t = φ t := fun g ↦ by rw [← hφ, ht]
  let := localizedGroupAction A (Localization.Away t) G t ht
  let := localizedGroupAction B (Localization.Away (φ t)) G (φ t) htB
  let : SMulDistribClass G A (Localization.Away t) :=
    smulDistribClass_localizedGroupAction A (Localization.Away t) G t ht
  let : SMulDistribClass G B (Localization.Away (φ t)) :=
    smulDistribClass_localizedGroupAction B (Localization.Away (φ t)) G (φ t) htB
  exact localizedRingMap_equivariant A B (Localization.Away t) (Localization.Away (φ t)) G φ hφ t

end Canonical
end AllCharacteristics
