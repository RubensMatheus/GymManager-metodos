/* GymManager
 * Author: ruben & JVSaraiva
 * Creation date: 14/05/2025
 */
MACHINE GymManager
    
SETS 
    MEMBER; 
    PERSONAL; 
    PLAN; 
    PAYMENT;
    WORKOUT; 
    MACHINES; 
    MACHINES_STATUS = {maintenance, available}

VARIABLES
    associated, follow, debtor_member

INVARIANT
    associated : MEMBER +-> PLAN
    & follow : MEMBER +-> PERSONAL
    & debtor_member <: MEMBER

INITIALISATION
    associated, follow, debtor_member := {}, {}, {}

OPERATIONS

add_member(member, plan) =
    PRE member : MEMBER & plan : PLAN & member /: dom(associated)
    THEN associated := associated \/ {member |-> plan}
    END;
    
cancel_member(member) =
    PRE member : MEMBER
    THEN
    associated := {member} <<| associated ||
    follow := {member} <<| follow ||
    debtor_member := debtor_member - {member} 
    END

END
