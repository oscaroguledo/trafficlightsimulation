mtype = {DANGER, PROCEED};

chan signal_north = [1] of {mtype};
chan signal_south = [1] of {mtype};
chan signal_east = [1] of {mtype};
chan signal_west = [1] of {mtype};

proctype NorthTrafficLight() {
    mtype ASPECT = PROCEED;  // Initial aspect is DANGER

    do
    :: signal_north ? PROCEED ->
        ASPECT = PROCEED;
        printf("North Traffic Light: Switched to PROCEED\n");
    :: signal_north ? DANGER ->
        ASPECT = DANGER;
        printf("North Traffic Light: Switched to DANGER\n");
    od;
}

proctype SouthTrafficLight() {
    mtype ASPECT = PROCEED;  // Initial aspect is DANGER

    do
    :: signal_south ? PROCEED ->
        ASPECT = PROCEED;
        printf("South Traffic Light: Switched to PROCEED\n");
    :: signal_south ? DANGER ->
        ASPECT = DANGER;
        printf("South Traffic Light: Switched to DANGER\n");
    od;
}

proctype EastTrafficLight() {
    mtype ASPECT = DANGER;  // Initial aspect is DANGER

    do
    :: signal_east ? PROCEED ->
        ASPECT = PROCEED;
        printf("East Traffic Light: Switched to PROCEED\n");
    :: signal_east ? DANGER ->
        ASPECT = DANGER;
        printf("East Traffic Light: Switched to DANGER\n");
    od;
}

proctype WestTrafficLight() {
    mtype ASPECT = DANGER;  // Initial aspect is DANGER

    do
    :: signal_west ? PROCEED ->
        ASPECT = PROCEED;
        printf("West Traffic Light: Switched to PROCEED\n");
    :: signal_west ? DANGER ->
        ASPECT = DANGER;
        printf("West Traffic Light: Switched to DANGER\n");
    od;
}

proctype CentralControl() {
    do
    :: true ->
        if
        :: signal_north == PROCEED ->
            signal_north ! DANGER;  // Instruct North traffic light to danger if on proceed
        :: else ->
            signal_north ! PROCEED;  // Instruct North traffic light to proceed otherwise
        fi;

        if
        :: signal_south == PROCEED ->
            signal_south ! DANGER;  // Instruct South traffic light to danger if on proceed
        :: else ->
            signal_south ! PROCEED;  // Instruct South traffic light to proceed otherwise
        fi;

        if
        :: signal_east == PROCEED ->
            signal_east ! DANGER;  // Instruct East traffic light to danger if on proceed
        :: else ->
            signal_east ! PROCEED;  // Instruct East traffic light to proceed otherwise
        fi;

        if
        :: signal_west == PROCEED ->
            signal_west ! DANGER;  // Instruct West traffic light to danger if on proceed
        :: else ->
            signal_west ! PROCEED;  // Instruct West traffic light to proceed otherwise
        fi;

        // Sleep or delay to allow traffic light update
        atomic {
            skip // Placeholder for a delay or to simulate time passing
        }
    od;
}




init {
    atomic {
        run NorthTrafficLight();
        run SouthTrafficLight();
        run EastTrafficLight();
        run WestTrafficLight();
        run CentralControl();
    }
}

