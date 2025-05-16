/* GymManager
 * Author: ruben & JVSaraiva
 * Creation date: 14/05/2025
 */
MACHINE GymManager
    
SETS 
    USER;
    PLAN; 
    PAYMENT;
    WORKOUT; 
    MACHINES; 
    MACHINES_STATUS = {maintenance, available}

VARIABLES
    associated, follow, debtor_member, member, personal, trains, day_workout, personal_workout

INVARIANT
    member <: USER
    & personal <: USER 
    & trains : member +-> personal
    & associated : member +-> PLAN 
    & follow : member +-> personal
    & debtor_member <: member
    & personal_workout : personal +-> WORKOUT
    & day_workout : member +-> WORKOUT

INITIALISATION
    associated, follow, debtor_member, member, personal, trains, day_workout, personal_workout := {}, {}, {}, {}, {}, {}, {}, {}

OPERATIONS

add_member(mm, plan) =
    PRE mm : USER & mm : member & plan : PLAN & mm /: dom(associated)
    THEN associated := associated \/ {mm |-> plan}
    END;
    
cancel_member(mm) =
    PRE mm : USER & mm : member
    THEN
    associated := {mm} <<| associated ||
    follow := {mm} <<| follow ||
    debtor_member := debtor_member - {mm} 
    END;
   
register_personal(pp) =
    PRE pp : USER & pp : personal
    THEN personal := personal \/ {pp}
    END;

link_personal(pp, mm) =
    PRE mm : USER & mm : member & pp : USER & pp : personal & (mm |-> pp) /: trains
    THEN 
       IF mm : dom(trains)
        THEN trains := ({mm} <<| trains) \/ {mm |-> pp}
       ELSE
        trains := trains \/ {mm |-> pp}
       END
    END;

unlink_personal(pp, mm) =
    PRE mm : USER & mm : member & pp : USER & pp : personal & (mm |-> pp) : trains
    THEN trains := trains - {mm |-> pp}
    END;

assign_workout(pp, mm, ww) =
    PRE mm : USER & mm : member & pp : USER & pp : personal & (mm |-> pp) : trains
    & ww : WORKOUT & (pp |-> ww) : personal_workout & (mm |-> ww) : day_workout
    THEN day_workout := day_workout \/ {mm |-> ww}
    END

END
