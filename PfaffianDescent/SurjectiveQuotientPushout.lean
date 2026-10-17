import PfaffianDescent.QuotientSupPushout

/-!
# Pushouts from surjective quotient maps

If a commutative square of surjective ring maps has target kernel equal to
the sum of the two side kernels, then it is a pushout. This formulation is
suited to the actual coordinate rings of projective affine charts.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits

universe u
set_option backward.isDefEq.respectTransparency false
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

theorem isPushout_of_surjective_ker_sup
    (f : A →+* B) (g : A →+* C) (l : B →+* D) (r : C →+* D)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hl : Function.Surjective l)
    (hcomp : l.comp f = r.comp g)
    (hker : RingHom.ker (l.comp f) = RingHom.ker f ⊔ RingHom.ker g) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom l) (CommRingCat.ofHom r) := by
  let h := l.comp f
  have hh : Function.Surjective h := hl.comp hf
  have w : CommRingCat.ofHom f ≫ CommRingCat.ofHom l =
      CommRingCat.ofHom g ≫ CommRingCat.ofHom r := by
    apply CommRingCat.hom_ext
    exact hcomp
  let desc : (s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom g)) →
      CommRingCat.of D ⟶ s.pt := by
    intro s
    let v : A →+* s.pt := s.inl.hom.comp f
    have hI : RingHom.ker f ≤ RingHom.ker v := by
      intro a ha
      change s.inl.hom (f a) = 0
      exact (show f a = 0 from ha) ▸ map_zero _
    have hJ : RingHom.ker g ≤ RingHom.ker v := by
      intro a ha
      change v a = 0
      have hc := congrArg (fun z : CommRingCat.of A ⟶ s.pt => z.hom a) s.condition
      have hc' : v a = s.inr.hom (g a) := by
        simpa [v, CommRingCat.hom_comp] using hc
      rw [show g a = 0 from ha, map_zero] at hc'
      exact hc'
    have hv : RingHom.ker h ≤ RingHom.ker v := by
      rw [hker]
      exact sup_le hI hJ
    exact CommRingCat.ofHom
      ((Ideal.Quotient.lift (RingHom.ker h) v (fun a ha => hv ha)).comp
        (RingHom.quotientKerEquivOfSurjective hh).symm.toRingHom)
  apply IsPushout.of_isColimit (c := PushoutCocone.mk
    (CommRingCat.ofHom l) (CommRingCat.ofHom r) w)
  refine PushoutCocone.IsColimit.mk w desc ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hf x
    simp only [desc, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom]
    change (Ideal.Quotient.lift (RingHom.ker h) _ _)
      ((RingHom.quotientKerEquivOfSurjective hh).symm (h a)) = _
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply hh,
      Ideal.Quotient.lift_mk]
    rfl
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hg x
    have hc := congrArg (fun z : CommRingCat.of A ⟶ s.pt => z.hom a) s.condition
    simp only [desc, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom]
    change (Ideal.Quotient.lift (RingHom.ker h) _ _)
      ((RingHom.quotientKerEquivOfSurjective hh).symm
        ((r.comp g) a)) = _
    rw [← hcomp]
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply hh,
      Ideal.Quotient.lift_mk]
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom] using hc
  · intro s m hmleft _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hh x
    have hc := congrArg (fun z : CommRingCat.of B ⟶ s.pt => z.hom (f a)) hmleft
    simp only [desc, RingHom.comp_apply,
      CommRingCat.hom_ofHom]
    change _ = (Ideal.Quotient.lift (RingHom.ker h) _ _)
      ((RingHom.quotientKerEquivOfSurjective hh).symm (h a))
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply hh,
      Ideal.Quotient.lift_mk]
    simpa only [h, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom] using hc

end PfaffianDescent
