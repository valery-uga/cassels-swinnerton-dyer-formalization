import PfaffianDescent.CorayPerfectFiniteTypeFrobenius
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.Noetherian.Basic

/-! SOURCE ONLY / UNVERIFIED. Construct the ACTUAL power-root envelope of
an embedded subalgebra inside the SAME field. Its literal power map and
scalar law embed its ordinary module into the Frobenius-restricted regular
module. Finite-type over original perfect K derives this target's finiteness
by accepted source084; no desired envelope/normalization finiteness premise. -/
noncomputable section
namespace PfaffianDescent.Coray
universe u v
variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The actual T-subalgebra of SAME L whose p^n powers belong to the
actual embedded T. The usual T coefficient inclusion is retained. -/
def powerRootEnvelope (T : Subalgebra K L) (p : ℕ) [ExpChar K p] (n : ℕ) :
    Subalgebra T L := by
  letI : ExpChar L p :=
    expChar_of_injective_ringHom (algebraMap K L).injective p
  exact
    { carrier := {x | x ^ (p ^ n) ∈ T}
      zero_mem' := by
        change (0 : L) ^ (p ^ n) ∈ T
        rw [zero_pow (pow_ne_zero n (expChar_ne_zero K p))]
        exact T.zero_mem
      one_mem' := by
        change (1 : L) ^ (p ^ n) ∈ T
        rw [one_pow]
        exact T.one_mem
      add_mem' := by
        intro x y hx hy
        change (x + y) ^ (p ^ n) ∈ T
        rw [add_pow_expChar_pow]
        exact T.add_mem hx hy
      mul_mem' := by
        intro x y hx hy
        change (x * y) ^ (p ^ n) ∈ T
        rw [mul_pow]
        exact T.mul_mem hx hy
      algebraMap_mem' := by
        intro t
        change (t : L) ^ (p ^ n) ∈ T
        exact T.pow_mem t.property _ }

/-- The power is already in actual T by envelope membership, so no choice
of root, replacement ambient field or supplied reduction map is needed. -/
def powerRootEnvelopePowerMap (T : Subalgebra K L)
    (p : ℕ) [ExpChar K p] (n : ℕ) : powerRootEnvelope T p n →+* T := by
  letI : ExpChar L p :=
    expChar_of_injective_ringHom (algebraMap K L).injective p
  exact
    { toFun := fun x => ⟨(x : L) ^ (p ^ n), x.property⟩
      map_zero' := by
        apply Subtype.ext
        exact zero_pow (pow_ne_zero n (expChar_ne_zero K p))
      map_one' := by
        apply Subtype.ext
        exact one_pow _
      map_add' := by
        intro x y
        apply Subtype.ext
        exact add_pow_expChar_pow (x : L) (y : L) p n
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact mul_pow (x : L) (y : L) _ }

/-- The actual usual T-action on the envelope has the literal Frobenius
scalar law. This is an equality in actual T, not a supplied certificate. -/
theorem powerRootEnvelopePowerMap_smul (T : Subalgebra K L)
    (p : ℕ) [ExpChar K p] (n : ℕ) :
    letI : ExpChar T p :=
      expChar_of_injective_ringHom (algebraMap K T).injective p
    ∀ (t : T) (x : powerRootEnvelope T p n),
      powerRootEnvelopePowerMap T p n (t • x) =
        iterateFrobenius T p n t * powerRootEnvelopePowerMap T p n x := by
  letI : ExpChar T p :=
    expChar_of_injective_ringHom (algebraMap K T).injective p
  intro t x
  apply Subtype.ext
  change ((t : L) * (x : L)) ^ (p ^ n) =
    (t : L) ^ (p ^ n) * (x : L) ^ (p ^ n)
  exact mul_pow _ _ _

private theorem powerRootEnvelopePowerMap_injective (T : Subalgebra K L)
    (p : ℕ) [ExpChar K p] (n : ℕ) :
    Function.Injective (powerRootEnvelopePowerMap T p n) := by
  letI : ExpChar L p :=
    expChar_of_injective_ringHom (algebraMap K L).injective p
  intro x y h
  apply Subtype.ext
  apply iterateFrobenius_inj L p n
  exact congrArg (fun t : T => (t : L)) h

/-- Finite-type of actual embedded T over ORIGINAL perfect K derives a
finite power-root envelope in SAME L. The auxiliary target is explicitly
the regular module restricted through the literal power map; the envelope
retains its ordinary actual T-action throughout. -/
theorem perfectField_finiteType_powerRootEnvelope_finite [PerfectField K]
    (T : Subalgebra K L) [Algebra.FiniteType K T]
    (p : ℕ) [ExpChar K p] (n : ℕ) :
    Module.Finite T (powerRootEnvelope T p n) := by
  letI : ExpChar T p :=
    expChar_of_injective_ringHom (algebraMap K T).injective p
  let M : ModuleCat.{v} T :=
    (ModuleCat.restrictScalars (iterateFrobenius T p n)).obj (ModuleCat.of T T)
  have hpower : (iterateFrobenius T p n).Finite :=
    perfectField_finiteType_iterateFrobenius_finite K T p n
  letI : Module.Finite T M := by
    change (iterateFrobenius T p n).Finite
    exact hpower
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  letI : IsNoetherian T M := inferInstance
  let f : powerRootEnvelope T p n →ₗ[T] M := by
    refine
      { toFun := fun x => powerRootEnvelopePowerMap T p n x
        map_add' := fun x y => (powerRootEnvelopePowerMap T p n).map_add x y
        map_smul' := ?_ }
    intro t x
    change powerRootEnvelopePowerMap T p n (t • x) =
      iterateFrobenius T p n t * powerRootEnvelopePowerMap T p n x
    exact powerRootEnvelopePowerMap_smul T p n t x
  have hf : Function.Injective f := powerRootEnvelopePowerMap_injective T p n
  exact Module.Finite.of_injective f hf

end PfaffianDescent.Coray
