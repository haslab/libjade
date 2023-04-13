# Notes about Keccak1600 implementations

* `spec`  - "specification" implementation; performance is not a concern; suffix: spec;
* `ref`   - uses stack in internal functions: no local function for keccakf; suffix: ref;
* `ref1`  - uses reg ptr and defines local function for keccakf; suffix: ref1;
* `bmi1`  - same as previous and uses andn instruction (faster than ref1 ~20%; not all cpus support bmi1); suffix: ref1 (to be interchangeable with ref1).
