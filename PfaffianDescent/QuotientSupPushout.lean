import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotient by an ideal sum as an affine intersection

The two quotient maps from a commutative ring push out to the quotient by
the sum of their kernels. Applying `Spec` gives the affine-chart pullback
needed for intersections of projective hypersurfaces.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] (I J : Ideal A)

def quotientSupFromLeft :
    CommRingCat.of (A ⧸ I) ⟶ CommRingCat.of (A ⧸ I ⊔ J) :=
  CommRingCat.ofHom (Ideal.Quotient.factor le_sup_left)

def quotientSupFromRight :
    CommRingCat.of (A ⧸ J) ⟶ CommRingCat.of (A ⧸ I ⊔ J) :=
  CommRingCat.ofHom (Ideal.Quotient.factor le_sup_right)

/-- The quotient by `I ⊔ J` is the pushout of the two quotient maps. -/
theorem isPushout_quotientSup :
    IsPushout
      (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (quotientSupFromLeft I J) (quotientSupFromRight I J) := by
  let f : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let g : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J) :=
    CommRingCat.ofHom (Ideal.Quotient.mk J)
  let l := quotientSupFromLeft I J
  let r := quotientSupFromRight I J
  have w : f ≫ l = g ≫ r := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  let desc : (s : PushoutCocone f g) → CommRingCat.of (A ⧸ I ⊔ J) ⟶ s.pt := by
    intro s
    let u : A →+* s.pt := s.inl.hom.comp (Ideal.Quotient.mk I)
    have hI : I ≤ RingHom.ker u := by
      intro a ha
      change u a = 0
      simp [u, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    have hJ : J ≤ RingHom.ker u := by
      intro a ha
      change u a = 0
      have hc := congrArg (fun z : CommRingCat.of A ⟶ s.pt => z.hom a) s.condition
      have hc' : u a = s.inr.hom ((Ideal.Quotient.mk J) a) := by
        simpa [f, g, u] using hc
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at hc'
      exact hc'
    have hu : ∀ a ∈ I ⊔ J, u a = 0 := by
      intro a ha
      exact (sup_le hI hJ) ha
    exact CommRingCat.ofHom (Ideal.Quotient.lift (I ⊔ J) u hu)
  change IsPushout f g l r
  apply IsPushout.of_isColimit (c := PushoutCocone.mk l r w)
  refine PushoutCocone.IsColimit.mk w desc ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [desc, l, quotientSupFromLeft, CommRingCat.hom_comp,
      RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.lift_mk]
    rfl
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hc := congrArg (fun z : CommRingCat.of A ⟶ s.pt => z.hom a) s.condition
    simp only [desc, r, quotientSupFromRight, CommRingCat.hom_comp,
      RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.lift_mk]
    simpa only [f, g, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom] using hc
  · intro s m hmleft _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hc := congrArg (fun z : CommRingCat.of (A ⧸ I) ⟶ s.pt => z.hom
      ((Ideal.Quotient.mk I) a)) hmleft
    simp only [desc, CommRingCat.hom_ofHom]
    rw [Ideal.Quotient.lift_mk]
    simpa only [l, quotientSupFromLeft, CommRingCat.hom_comp,
      RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk] using hc

/-- The corresponding affine spectra form the actual fibre product. -/
theorem isPullback_spec_quotientSup :
    IsPullback
      (Spec.map (quotientSupFromLeft I J))
      (Spec.map (quotientSupFromRight I J))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotientSup I J)

end PfaffianDescent
