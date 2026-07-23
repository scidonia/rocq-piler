Feature: Stateful opaque specs (FunSpecS)
  The function table supports opaque specs whose pre/post quantify over
  the heap state, with results reified as values or exceptions and
  state changes applied as explicit cell updates.  Each scenario below
  is machine-checked by a Coq Example of the same name in
  coq/SnakeletExnSpecSDemo.v (run: coqc -R coq "" coq/SnakeletExnSpecSDemo.v).

  Rule: Opaque calls only step when the precondition holds — calling
  outside the precondition is stuck, and state changes are explicit
  cell updates, never arbitrary.

  Scenario: A stateful spec steps with explicit cell updates
    Given a spec "bump" whose precondition requires the cell to hold an integer
    And a heap where the cell holds the integer n
    When "bump" is called with the cell as argument
    Then the call returns n
    And the cell is updated to n + 1, everything else unchanged
    Checked by: bump_steps

  Scenario: Precondition violation is stuck
    Given a spec "bump" whose precondition requires the cell to hold an integer
    And a heap where the cell is missing
    When "bump" is called with the cell as argument
    Then the call is stuck — no step exists
    Checked by: bump_stuck_when_cell_missing

  Scenario: An exceptional post raises with label and payload
    Given a spec "fail" whose post is the exception IntegrityError "duplicate key"
    When "fail" is called
    Then the call steps to an uncaught raise carrying the label and payload
    And the terminal result reads off as that exception
    Checked by: fail_steps_to_raise, fail_result_is_exception

  Scenario: Totality is a table-level obligation
    Given the demo table with entries "bump" and "fail"
    Then every spec with a satisfiable precondition has a post-satisfying
    outcome with in-domain cell updates
    Checked by: specS_demo_table_total (discharged at instance declaration)
