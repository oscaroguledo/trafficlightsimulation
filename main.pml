mtype = {DANGER, PROCEED};

chan signal_north = [1] of {mtype};
chan signal_south = [1] of {mtype};
chan signal_east = [1] of {mtype};
chan signal_west = [1] of {mtype};

// Code for the TrafficMonitor process...
#define NorthSouthProceed (signal_north == PROCEED && signal_south == PROCEED)
#define WestEastProceed (signal_west == PROCEED && signal_east == PROCEED)

proctype TrafficMonitor() {
    do
    :: NorthSouthProceed || WestEastProceed ->
        printf("Invariant violation: Conflicting traffic signals detected!\n");
        assert(0); // Assertion failure on violation
    od;
}

// 4 Traffic light processes...
proctype NorthTrafficLight() {
    mtype ASPECT = PROCEED;  // Initial aspect is PROCEED

    do
    :: true ->
        if
        :: signal_north ? PROCEED ->
            ASPECT = PROCEED;
            printf("North Traffic Light: Switched to PROCEED\n");
        :: signal_north ? DANGER ->
            ASPECT = DANGER;
            printf("North Traffic Light: Switched to DANGER\n");
        fi;
    od;
}

proctype SouthTrafficLight() {
    mtype ASPECT = PROCEED;  // Initial aspect is PROCEED

    do
    :: true ->
        if
        :: signal_south ? PROCEED ->
            ASPECT = PROCEED;
            printf("South Traffic Light: Switched to PROCEED\n");
        :: signal_south ? DANGER ->
            ASPECT = DANGER;
            printf("South Traffic Light: Switched to DANGER\n");
        fi;
    od;
}


proctype EastTrafficLight() {
    mtype ASPECT = DANGER;  // Initial aspect is DANGER

    do
    :: true ->
        if
        :: signal_east ? PROCEED ->
            ASPECT = PROCEED;
            printf("East Traffic Light: Switched to PROCEED\n");
        :: signal_east ? DANGER ->
            ASPECT = DANGER;
            printf("East Traffic Light: Switched to DANGER\n");
        fi;
    od;
}

proctype WestTrafficLight() {
    mtype ASPECT = DANGER;  // Initial aspect is DANGER

    do
    :: true ->
        if
        :: signal_west ? PROCEED ->
            ASPECT = PROCEED;
            printf("West Traffic Light: Switched to PROCEED\n");
        :: signal_west ? DANGER ->
            ASPECT = DANGER;
            printf("West Traffic Light: Switched to DANGER\n");
        fi;
    od;
}

// Code for the CentralControl process...
proctype CentralControl() {
    bool ns_green = true;
    do
    :: ns_green ->  
        signal_north!PROCEED;
        signal_south!PROCEED;
        
        signal_east!DANGER;
        signal_west!DANGER;
        
        ns_green = false;
    :: else ->
        signal_north!DANGER;
        signal_south!DANGER;

        signal_east!PROCEED; 
        signal_west!PROCEED;
        
        ns_green = true;
    od;
}


// LTL safety constraint properties
ltl safetyConstraint { [](! (NorthSouthProceed || WestEastProceed)) }

// response properties
ltl responseProperty1 { [] (signal_north == PROCEED -> <> (signal_north == DANGER)) }
ltl responseProperty2 { [] (signal_south == PROCEED -> <> (signal_south == DANGER)) }
ltl responseProperty3 { [] (signal_east == PROCEED -> <> (signal_east == DANGER)) }
ltl responseProperty4 { [] (signal_west == PROCEED -> <> (signal_west == DANGER)) }


init {
    atomic {
        run NorthTrafficLight();
        run SouthTrafficLight();
        run EastTrafficLight();
        run WestTrafficLight();
        run TrafficMonitor();
        run CentralControl();
    }
}

