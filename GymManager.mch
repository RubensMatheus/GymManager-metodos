/* GymManager
 * Author: ruben & JVSaraiva
 * Creation date: 14/05/2025
 */
MACHINE GymManager
    
SETS 
    USER; 
    PLAN = {monthly, quarterly, yearly};
    WORKOUT; 
    MACHINES;
    MACHINES_STATUS = {maintenance, available};
    PRESENCE_STATUS = {present, not_present}

VARIABLES
    associated, member, debtor_member, personal, payment, plan_prices, presence, trains, day_workout, personal_workout, workout_history, machine_status, machines, general_workout

INVARIANT
    member <: USER
    & debtor_member <: member
    & personal <: USER 
    & associated : member --> PLAN 
    & payment : member --> 0..12
    & dom(associated) = dom(payment)
    & plan_prices : PLAN --> NAT1
    & presence : member --> PRESENCE_STATUS
    & dom(associated) = dom(presence)
    & trains : member +-> personal
    & general_workout <: WORKOUT
    & personal_workout : personal <-> WORKOUT
    & day_workout : member +-> WORKOUT 
    & workout_history : member <-> WORKOUT
    & machines <: MACHINES
    & machine_status : machines --> MACHINES_STATUS 

INITIALISATION
    associated, member, debtor_member, personal, payment, presence, trains, day_workout, personal_workout, workout_history, machine_status, machines, general_workout := {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {} ||
    plan_prices := {monthly |-> 50, quarterly |-> 135, yearly |-> 480}

OPERATIONS

add_member(uu, plan) =
    PRE 
        uu : USER 
        & uu /: member 
        & plan : PLAN
    THEN 
        member := member \/ {uu} ||
        associated := associated <+ {uu |-> plan} ||
        payment := payment <+ {uu |-> 0} ||
        presence := presence <+ { uu |-> not_present }
    END;

cancel_member(mm) =
    PRE 
        mm : member 
        & {mm} <<| associated : member - ({mm}) --> PLAN
        & {mm} <<| presence : member - ({mm}) --> PRESENCE_STATUS
        & {mm} <<| workout_history : member - ({mm}) <-> WORKOUT
    THEN
        member := member - {mm} ||
        associated := {mm} <<| associated ||
        trains := {mm} <<| trains ||
        payment := {mm} <<| payment ||
        presence := {mm} <<| presence ||
        debtor_member := debtor_member - {mm} ||
        day_workout := {mm} <<| day_workout ||
        workout_history := {mm} <<| workout_history
    END;

the_month =
  BEGIN
  
    payment := payment <+ %mm.( mm : member & payment(mm) > 0 | payment(mm) - 1) ||
  
    debtor_member := {mm | mm : member & payment(mm) <= 1}
  END;


change_plan_price(plan, new_price) =
    PRE 
        plan : PLAN 
        & new_price : NAT1
    THEN 
        plan_prices := plan_prices <+ {plan |-> new_price}
    END;
    
migrate_member_plan(mm, new_plan) =
    PRE 
        mm : member
        & new_plan : PLAN
        & new_plan /= associated(mm)
    THEN
        associated := associated <+ {mm |-> new_plan}
    END;

record_payment(mm, value) =
    PRE 
        mm : member 
        & value : NAT1
        & value = (associated;plan_prices)(mm)
        & payment(mm) = 0
    THEN 
        IF associated(mm) = monthly
            THEN payment(mm) := payment(mm) + 1
        ELSIF associated(mm) = quarterly
            THEN payment(mm) := payment(mm) + 3
        ELSE payment(mm) := payment(mm) + 12
        END
    END;
    
debtors <-- list_debtors = 
    BEGIN
        debtors := debtor_member 
    END;

check_in(mm) =
    PRE 
        mm : member 
        & mm /: debtor_member 
        & presence(mm) /= present
    THEN
        presence := presence <+ { mm |-> present }
    END;
    
check_out(mm) =
    PRE 
        mm : member 
        & mm /: debtor_member 
        & presence(mm) /= not_present
    THEN
        presence := presence <+ { mm |-> not_present }
    END;

training <-- list_present = 
    BEGIN
        training := dom(presence |> {present})
    END;

register_personal(pp) =
    PRE 
        pp : USER
        & pp /: personal
        & pp /: member
    THEN 
        personal := personal \/ {pp}
    END;

link_personal(pp, mm) =
    PRE  
        mm : member
        & mm /: debtor_member
        & pp : personal 
        & (mm |-> pp) /: trains
    THEN 
       IF mm : dom(trains)
        THEN trains := ({mm} <<| trains) \/ {mm |-> pp}
       ELSE
        trains := trains \/ {mm |-> pp}
       END
    END;

unlink_personal(pp, mm) =
    PRE 
        mm : member
        & pp : personal 
        & (mm |-> pp) : trains
    THEN 
        trains := trains - {mm |-> pp}
    END;

create_personal_workout(pp, ww) =
    PRE 
        pp : personal 
        & ww : WORKOUT
        & ww /: general_workout
        & (pp |-> ww) /: personal_workout
    THEN personal_workout := personal_workout \/ {pp |-> ww}
    END;

assign_personal_workout(pp, mm, ww) =
    PRE 
        mm : member 
        & mm /: debtor_member
        & pp : personal 
        & (mm |-> pp) : trains
        & ww : WORKOUT 
        & (pp |-> ww) : personal_workout 
        & (mm |-> ww) /: day_workout
    THEN 
        day_workout := {mm |-> ww} || 
        workout_history := workout_history \/ { mm |-> ww }
    END;
    
create_general_workout (ww) =
    PRE
       ww : WORKOUT
       & ww /: ran(personal_workout |> {ww})
    THEN 
        general_workout := general_workout \/ {ww}
    END;

assign_workout (mm, ww) =
    PRE 
        mm : member
        & mm /: debtor_member
        & ww : general_workout
    THEN 
        day_workout := {mm |-> ww} || 
        workout_history := workout_history \/ { mm |-> ww }
    END;

work <--current_workout(mm) = 
    PRE 
        mm : member
        & mm /: debtor_member
        & mm : dom(day_workout)
    THEN
        work := day_workout(mm)
    END;

history <-- workouts_history(mm) =
    PRE  
        mm : member
        & mm /: debtor_member
    THEN 
        history := { ww | ww : WORKOUT & (mm |-> ww) : workout_history }
    END;

add_machine (ma) =
    PRE 
        ma : MACHINES 
        & ma /: machines 
        & ma /: dom(machine_status)
    THEN 
        machines := machines \/ {ma} || 
        machine_status := machine_status \/ {ma |-> available}
    END;

remove_machine (ma) =
    PRE 
        ma : machines 
        & ma : dom(machine_status)
        & {ma} <<| machine_status : machines - ({ma}) --> MACHINES_STATUS
    THEN 
        machines := machines - {ma} || 
        machine_status := {ma} <<| machine_status 
    END;

set_equipment_status(ma, status) =
    PRE 
        ma : machines 
        & status : MACHINES_STATUS 
        & (ma |-> status) /: machine_status
    THEN 
        machine_status := machine_status <+ { ma |-> status }
    END;

status <-- get_equipment_status(ma) =
    PRE 
        ma : machines 
    THEN 
        status := machine_status(ma)
    END;


//---------------------Operaçãoes de pré-condição---------------------


ok <-- pre_add_member(uu, plan) =
  PRE
    uu : USER
    & uu /: member
    & plan : PLAN
  THEN
    IF uu : USER & uu /: member & plan : PLAN THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_cancel_member(mm) =
  PRE
    mm : member
    & {mm} <<| associated : member - ({mm}) --> PLAN
    & {mm} <<| presence : member - ({mm}) --> PRESENCE_STATUS
    & {mm} <<| workout_history : member - ({mm}) <-> WORKOUT
  THEN
    IF
      mm : member
      & {mm} <<| associated : member - ({mm}) --> PLAN
      & {mm} <<| presence : member - ({mm}) --> PRESENCE_STATUS
      & {mm} <<| workout_history : member - ({mm}) <-> WORKOUT
    THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;
  
ok <-- pre_the_month =
    BEGIN
        ok := TRUE
    END;

ok <-- pre_change_plan_price(plan, new_price) =
  PRE
    plan : PLAN
    & new_price : NAT1
  THEN
    IF plan : PLAN & new_price : NAT1 THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_migrate_member_plan(mm, new_plan) =
  PRE
    mm : member
    & new_plan : PLAN
    & new_plan /= associated(mm)
  THEN
    IF mm : member & new_plan : PLAN & new_plan /= associated(mm) THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_record_payment(mm, value) =
  PRE
    mm : member
    & value : NAT1
    & value = (associated;plan_prices)(mm)
    & payment(mm) = 0
  THEN
    IF mm : member & value : NAT1 & value = (associated;plan_prices)(mm) & payment(mm) = 0 THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_list_debtors =
  BEGIN
    ok := TRUE
  END;

ok <-- pre_check_in(mm) =
  PRE
    mm : member
    & mm /: debtor_member
    & presence(mm) /= present
  THEN
    IF mm : member & mm /: debtor_member & presence(mm) /= present THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_check_out(mm) =
  PRE
    mm : member
    & mm /: debtor_member
    & presence(mm) /= not_present
  THEN
    IF mm : member & mm /: debtor_member & presence(mm) /= not_present THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_list_present =
  BEGIN
    ok := TRUE
  END;

ok <-- pre_register_personal(pp) =
  PRE
    pp : USER
    & pp /: personal
    & pp /: member
  THEN
    IF pp : USER & pp /: personal & pp /: member THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_link_personal(pp, mm) =
  PRE
    mm : member
    & mm /: debtor_member
    & pp : personal
    & (mm |-> pp) /: trains
  THEN
    IF mm : member & mm /: debtor_member & pp : personal & (mm |-> pp) /: trains THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_unlink_personal(pp, mm) =
  PRE
    mm : member
    & pp : personal
    & (mm |-> pp) : trains
  THEN
    IF mm : member & pp : personal & (mm |-> pp) : trains THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;
  
ok <-- pre_create_personal_workout(pp, ww) =
  PRE
    pp : personal
    & ww : WORKOUT
    & ww /: general_workout
    & (pp |-> ww) /: personal_workout
  THEN
    IF pp : personal & ww : WORKOUT & ww /: general_workout & (pp |-> ww) /: personal_workout THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_assign_personal_workout(pp, mm, ww) =
  PRE
    mm : member
    & mm /: debtor_member
    & pp : personal
    & (mm |-> pp) : trains
    & ww : WORKOUT
    & (pp |-> ww) : personal_workout
    & (mm |-> ww) /: day_workout
  THEN
    IF mm : member
      & mm /: debtor_member
      & pp : personal
      & (mm |-> pp) : trains
      & ww : WORKOUT
      & (pp |-> ww) : personal_workout
      & (mm |-> ww) /: day_workout
    THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_create_general_workout(ww) =
  PRE
    ww : WORKOUT
    & ww /: ran(personal_workout |> {ww})
  THEN
    IF ww : WORKOUT & ww /: ran(personal_workout |> {ww}) THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_assign_workout(mm, ww) =
  PRE
    mm : member
    & mm /: debtor_member
    & ww : general_workout
  THEN
    IF mm : member & mm /: debtor_member & ww : general_workout THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_current_workout(mm) =
  PRE
    mm : member
    & mm /: debtor_member
    & mm : dom(day_workout)
  THEN
    IF mm : member & mm /: debtor_member & mm : dom(day_workout) THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_workouts_history(mm) =
  PRE
    mm : member
    & mm /: debtor_member
  THEN
    IF mm : member & mm /: debtor_member THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_add_machine(ma) =
  PRE
    ma : MACHINES
    & ma /: machines
    & ma /: dom(machine_status)
  THEN
    IF ma : MACHINES & ma /: machines & ma /: dom(machine_status) THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_remove_machine(ma) =
  PRE
    ma : machines
    & ma : dom(machine_status)
    & {ma} <<| machine_status : machines - ({ma}) --> MACHINES_STATUS
  THEN
    IF ma : machines & ma : dom(machine_status) & {ma} <<| machine_status : machines - ({ma}) --> MACHINES_STATUS THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_set_equipment_status(ma, status) =
  PRE
    ma : machines
    & status : MACHINES_STATUS
    & (ma |-> status) /: machine_status
  THEN
    IF ma : machines & status : MACHINES_STATUS & (ma |-> status) /: machine_status THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END;

ok <-- pre_get_equipment_status(ma) =
  PRE
    ma : machines
  THEN
    IF ma : machines THEN
      ok := TRUE
    ELSE
      ok := FALSE
    END
  END

END