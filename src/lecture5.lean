import data.nat.basic
import data.nat.parity
import tactic

namespace lecture5

set_option class.instance_max_depth 100

open nat

example {m : ℕ} (m_divd_14 : 14 ∣ m) : 7 ∣ (135 * m + 693) :=
begin
  cases m_divd_14 with i ih,
  refine dvd.intro _ _,
  use 270 * i + 99,
  rw ih,
  linarith,
end

end lecture5

