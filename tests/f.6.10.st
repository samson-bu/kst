FUNCTION_BLOCK PID
   VAR_INPUT
     AUTO : BOOL ;
     PV : REAL ;
     SP : REAL ;
     X0 : REAL ;

     KP : REAL ;
     TR : REAL ;
     TD : REAL ;
     CYCLE : REAL ;
   END_VAR
   VAR_OUTPUT XOUT : REAL; END_VAR
   VAR ERROR : REAL ;
       ITERM : INTEGRAL ;
       DTERM : DERIVATIVE ;
   END_VAR
   ERROR := PV - SP ;

   ITERM (RUN := AUTO, R1 := NOT AUTO, XIN := ERROR,
          X0 := TR * (X0 - ERROR), CYCLE := CYCLE) ;
   DTERM (RUN := AUTO, XIN := ERROR, CYCLE := CYCLE) ;
   XOUT := KP * (ERROR + ITERM.XOUT/TR + DTERM.XOUT*TD) ;
 END_FUNCTION_BLOCK