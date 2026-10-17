import AllCharacteristics.InvariantLocalizationNumerators

/-!
# The actual group action on localization at a fixed element

A group acting by ring automorphisms extends canonically to localization at an
element fixed by the group. The actual ring maps satisfy identity and
composition, and the resulting action is compatible with the original
coefficient action. No action on the localization is assumed.
-/

namespace AllCharacteristics
universe u v w
variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type w) [Group G] [MulSemiringAction G A]
variable (t : A) [IsLocalization.Away t B] (ht : ∀ g : G, g • t = t)

/-- Every original group element induces an actual ring endomorphism of the localization. -/
noncomputable def localizedGroupRingHom (g : G) : B →+* B :=
  IsLocalization.map B (MulSemiringAction.toRingHom G A g)
    (show Submonoid.powers t ≤ (Submonoid.powers t).comap
      (MulSemiringAction.toRingHom G A g) from by
      rintro a ⟨n, rfl⟩
      change g • t ^ n ∈ Submonoid.powers t
      rw [smul_pow', ht g]
      exact ⟨n, rfl⟩)

/-- The localized endomorphism acts on original coefficients by the original action. -/
theorem localizedGroupRingHom_algebraMap (g : G) (a : A) :
    localizedGroupRingHom A B G t ht g (algebraMap A B a) = algebraMap A B (g • a) :=
  IsLocalization.map_eq _ _

/-- The identity group element induces the identity map on the actual localization. -/
theorem localizedGroupRingHom_one :
    localizedGroupRingHom A B G t ht 1 = RingHom.id B := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  apply RingHom.ext
  intro a
  change localizedGroupRingHom A B G t ht 1 (algebraMap A B a) = algebraMap A B a
  rw [localizedGroupRingHom_algebraMap, one_smul]

/-- The localized coefficient maps respect multiplication in the original group. -/
theorem localizedGroupRingHom_mul (g h : G) :
    localizedGroupRingHom A B G t ht (g * h) =
      (localizedGroupRingHom A B G t ht g).comp (localizedGroupRingHom A B G t ht h) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  apply RingHom.ext
  intro a
  change localizedGroupRingHom A B G t ht (g * h) (algebraMap A B a) =
    localizedGroupRingHom A B G t ht g
      (localizedGroupRingHom A B G t ht h (algebraMap A B a))
  rw [localizedGroupRingHom_algebraMap, localizedGroupRingHom_algebraMap,
    localizedGroupRingHom_algebraMap, mul_smul]

/-- The actual multiplicative ring action induced on localization at a fixed denominator. -/
@[instance_reducible]
noncomputable def localizedGroupAction : MulSemiringAction G B where
  smul g b := localizedGroupRingHom A B G t ht g b
  one_smul b := congrArg (fun h : B →+* B ↦ h b) (localizedGroupRingHom_one A B G t ht)
  mul_smul g h b := congrArg (fun e : B →+* B ↦ e b) (localizedGroupRingHom_mul A B G t ht g h)
  smul_zero g := (localizedGroupRingHom A B G t ht g).map_zero
  smul_one g := (localizedGroupRingHom A B G t ht g).map_one
  smul_add g b c := (localizedGroupRingHom A B G t ht g).map_add b c
  smul_mul g b c := (localizedGroupRingHom A B G t ht g).map_mul b c

/-- The constructed localization action is compatible with the original coefficient action. -/
instance smulDistribClass_localizedGroupAction :
    letI := localizedGroupAction A B G t ht
    SMulDistribClass G A B := by
  let := localizedGroupAction A B G t ht
  constructor
  intro g a b
  simp only [Algebra.smul_def]
  change localizedGroupRingHom A B G t ht g (algebraMap A B a * b) =
    algebraMap A B (g • a) * localizedGroupRingHom A B G t ht g b
  rw [map_mul, localizedGroupRingHom_algebraMap]

end AllCharacteristics
