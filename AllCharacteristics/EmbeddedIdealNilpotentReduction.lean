import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Finiteness.Ideal

set_option pp.deepTerms true
set_option pp.funBinderTypes true


/-!
Whole-ideal reduction and finiteness of the actual embedded quotient.
No flatness or Hilbert-functor certificate is assumed or asserted.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AllCharacteristics
universe u v w

/-- The reduction of the prescribed embedded ideal, with its original scalar
action and its entire ideal image. -/
def embeddedIdealReduction165
    {T : Type u} {A' : Type v} {A : Type w}
    [CommRing T] [CommRing A'] [CommRing A]
    [Algebra T A'] [Algebra T A]
    (π : A' →ₐ[T] A) (J' : Ideal A') :
    (A' ⧸ J') →ₐ[T] (A ⧸ J'.map π.toRingHom) :=
  Ideal.quotientMapₐ (J'.map π.toRingHom) π Ideal.le_comap_map

/-- The quotient reduction commutes with the original ambient reduction. -/
theorem embeddedIdealReduction165_apply_mk
    {T : Type u} {A' : Type v} {A : Type w}
    [CommRing T] [CommRing A'] [CommRing A]
    [Algebra T A'] [Algebra T A]
    (π : A' →ₐ[T] A) (J' : Ideal A') (x : A') :
    embeddedIdealReduction165 π J' (Ideal.Quotient.mk J' x) =
      Ideal.Quotient.mk (J'.map π.toRingHom) (π x) := rfl

/-- Surjectivity is inherited from the given ambient reduction. -/
theorem embeddedIdealReduction165_surjective
    {T : Type u} {A' : Type v} {A : Type w}
    [CommRing T] [CommRing A'] [CommRing A]
    [Algebra T A'] [Algebra T A]
    (π : A' →ₐ[T] A) (hπ : Function.Surjective π) (J' : Ideal A') :
    Function.Surjective (embeddedIdealReduction165 π J') :=
  Ideal.quotientMap_surjective (H := Ideal.le_comap_map) hπ

/-- The reduction kernel in the actual quotient is exactly the image of the
whole ambient reduction kernel.  This fixes the entire special fiber. -/
theorem embeddedIdealReduction165_ker
    {T : Type u} {A' : Type v} {A : Type w}
    [CommRing T] [CommRing A'] [CommRing A]
    [Algebra T A'] [Algebra T A]
    (π : A' →ₐ[T] A) (hπ : Function.Surjective π) (J' : Ideal A') :
    RingHom.ker (embeddedIdealReduction165 π J').toRingHom =
      (RingHom.ker π.toRingHom).map (Ideal.Quotient.mk J') := by
  change RingHom.ker (Ideal.quotientMap (J'.map π.toRingHom)
    π.toRingHom Ideal.le_comap_map) = _
  rw [Ideal.quotientMap, Ideal.ker_quotient_lift, ← RingHom.comap_ker,
    Ideal.mk_ker, Ideal.comap_map_of_surjective π.toRingHom hπ,
    ← RingHom.ker_eq_comap_bot, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]

/-- A square-zero ambient reduction stays square-zero on the actual quotient. -/
theorem embeddedIdealReduction165_ker_square_zero
    {T : Type u} {A' : Type v} {A : Type w}
    [CommRing T] [CommRing A'] [CommRing A]
    [Algebra T A'] [Algebra T A]
    (π : A' →ₐ[T] A) (hπ : Function.Surjective π) (J' : Ideal A')
    (hK : (RingHom.ker π.toRingHom) ^ 2 = ⊥) :
    (RingHom.ker (embeddedIdealReduction165 π J').toRingHom) ^ 2 = ⊥ := by
  rw [embeddedIdealReduction165_ker π hπ J', ← Ideal.map_pow, hK, Ideal.map_bot]

/-- Finiteness of the prescribed reduced quotient lifts through a finitely
generated square-zero ambient kernel, without assuming finiteness of the
lifted quotient.  For a noetherian test algebra, finite generation follows
from the ambient kernel being the extension of its finitely generated base
ideal.  This conclusion asserts finiteness, not flatness. -/
theorem embeddedIdealReduction165_finite_of_square_zero
    {T : Type u} {A' : Type v} {A : Type w}
    [CommRing T] [CommRing A'] [CommRing A]
    [Algebra T A'] [Algebra T A]
    (π : A' →ₐ[T] A) (hπ : Function.Surjective π) (J' : Ideal A')
    [Module.Finite T (A ⧸ J'.map π.toRingHom)]
    (hKfg : (RingHom.ker π.toRingHom).FG)
    (hK : (RingHom.ker π.toRingHom) ^ 2 = ⊥) :
    Module.Finite T (A' ⧸ J') := by
  let ρ := embeddedIdealReduction165 π J'
  have hρK : (RingHom.ker ρ.toRingHom) ^ 2 = ⊥ :=
    embeddedIdealReduction165_ker_square_zero π hπ J' hK
  refine Module.finite_of_surjective_of_ker_le_nilradical ρ
    (embeddedIdealReduction165_surjective π hπ J') ?_ ?_
  · intro x hx
    apply mem_nilradical.mpr
    refine ⟨2, ?_⟩
    have hx2 := Ideal.pow_mem_pow hx 2
    change x ^ 2 ∈ (RingHom.ker ρ.toRingHom) ^ 2 at hx2
    rw [hρK] at hx2
    exact Ideal.mem_bot.mp hx2
  · change (RingHom.ker (embeddedIdealReduction165 π J').toRingHom).FG
    rw [embeddedIdealReduction165_ker π hπ J']
    exact hKfg.map (Ideal.Quotient.mk J')

end AllCharacteristics

