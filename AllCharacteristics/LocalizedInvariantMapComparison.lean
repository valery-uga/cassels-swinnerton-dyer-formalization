import AllCharacteristics.InvariantLocalization
import AllCharacteristics.InvariantRingEquivalence
import AllCharacteristics.LocalizedEquivariantMaps
import AllCharacteristics.AffineLocalizationPullback

/-!
# Comparison of localized quotient maps with invariants of localized maps

The canonical invariant-localization equivalences identify localization of
an induced invariant map with the invariant map of the actual localization.
Consequently a bijective equivariant localization induces a bijective
localization of the invariant-ring map. This is the local algebra needed
for the quotient overlap open immersions.
-/

namespace AllCharacteristics
universe u v
variable (R A B L M : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [CommRing L] [CommRing M]
variable [Algebra R A] [Algebra R B] [Algebra R L] [Algebra R M]
variable [Algebra A L] [Algebra B M]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [MulSemiringAction G L] [MulSemiringAction G M]
variable [SMulCommClass G R A] [SMulCommClass G R B]
variable [SMulCommClass G R L] [SMulCommClass G R M]
variable [SMulDistribClass G A L] [SMulDistribClass G B M]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)
variable (t : FixedPoints.subalgebra R A G)
variable [IsLocalization.Away t.val L] [IsLocalization.Away (φ t.val) M]

/-- Bijectivity of an actual equivariant localization descends to localization of its invariant map. -/
theorem localizedInvariantMap_bijective_of_bijective_localizedMap
    (hbij : Function.Bijective (IsLocalization.Away.map L M φ t.val)) :
    Function.Bijective (Localization.awayMap (equivariantInvariantMap R A B G φ hφ) t) := by
  let β := equivariantInvariantMap R A B G φ hφ
  let ψ := IsLocalization.Away.map L M φ t.val
  have hψ : ∀ (g : G) (z : L), ψ (g • z) = g • ψ z :=
    localizedRingMap_equivariant A B L M G φ hφ t.val
  let := equivariantFixedSubalgebraAlgebra R A L G
  let := equivariantFixedSubalgebraAlgebra R B M G
  have : IsLocalization.Away (β t).val M := by
    change IsLocalization.Away (φ t.val) M
    infer_instance
  let eA : Localization.Away t ≃+* FixedPoints.subalgebra R L G :=
    (invariantLocalizationAlgEquiv R A L G t).toRingEquiv
  let eB : Localization.Away (β t) ≃+* FixedPoints.subalgebra R M G :=
    (invariantLocalizationAlgEquiv R B M G (β t)).toRingEquiv
  let eC : FixedPoints.subalgebra R L G ≃+* FixedPoints.subalgebra R M G :=
    equivariantInvariantRingEquiv R L M G ψ hψ hbij
  have he : eB.toRingHom.comp (Localization.awayMap β t) = eC.toRingHom.comp eA.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    apply RingHom.ext
    intro a
    have hloc : Localization.awayMap β t
        (algebraMap (FixedPoints.subalgebra R A G) (Localization.Away t) a) =
          algebraMap (FixedPoints.subalgebra R B G) (Localization.Away (β t)) (β a) :=
      congrArg (fun h : FixedPoints.subalgebra R A G →+* Localization.Away (β t) ↦ h a)
        (awayMap_comp_algebraMap β t)
    have hA : eA (algebraMap (FixedPoints.subalgebra R A G) (Localization.Away t) a) =
        equivariantFixedSubalgebraMap R A L G a :=
      invariantLocalizationAlgEquiv_algebraMap R A L G t a
    have hB : eB (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away (β t)) (β a)) =
        equivariantFixedSubalgebraMap R B M G (β a) :=
      invariantLocalizationAlgEquiv_algebraMap R B M G (β t) (β a)
    change eB (Localization.awayMap β t
      (algebraMap (FixedPoints.subalgebra R A G) (Localization.Away t) a)) =
        eC (eA (algebraMap (FixedPoints.subalgebra R A G) (Localization.Away t) a))
    rw [hloc, hA, hB]
    apply Subtype.ext
    change algebraMap B M (φ a.val) =
      IsLocalization.Away.map L M φ t.val (algebraMap A L a.val)
    exact (localizedRingMap_algebraMap A B L M φ t.val a.val).symm
  let e := eA.trans (eC.trans eB.symm)
  have hmap : e.toRingHom = Localization.awayMap β t := by
    apply RingHom.ext
    intro z
    apply eB.injective
    change eB (eB.symm (eC (eA z))) = eB (Localization.awayMap β t z)
    rw [eB.apply_symm_apply]
    exact (congrArg (fun h : Localization.Away t →+* FixedPoints.subalgebra R M G ↦ h z) he).symm
  have hb : Function.Bijective e.toRingHom := e.bijective
  rw [hmap] at hb
  exact hb

end AllCharacteristics
