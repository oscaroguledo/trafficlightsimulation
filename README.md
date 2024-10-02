Here's a `README.md` for your traffic light system project, including your GitHub username:

---

# Traffic Light System with Invariant Monitoring

This project implements a traffic light control system that uses Promela (the language for modeling concurrent systems) and the SPIN model checker to ensure the safety of traffic signals at intersections. It checks for invariant violations to prevent conflicting traffic signals from being activated at the same time.

## Features

- **Traffic Light Control**: Simulates traffic lights for North, South, East, and West directions.
- **Invariant Monitoring**: Ensures that no conflicting traffic signals (e.g., North and South both showing green) occur.
- **Central Control**: Manages the switching of traffic signals based on a simple alternating strategy.
- **Safety and Response Properties**: Utilizes LTL (Linear Temporal Logic) to specify and verify properties of the traffic system.

## Getting Started

### Prerequisites

- SPIN Model Checker

### Running the Model

1. Ensure you have the SPIN Model Checker installed on your system. You can download it from [the SPIN website](http://spinroot.com/spin/whatispin.html).

2. Save the Promela code in a file named `traffic_light.pml`.

3. Open a terminal and navigate to the directory containing `traffic_light.pml`.

4. Run the SPIN model checker:

```bash
spin -a traffic_light.pml      # Generate the C code
gcc -o pan pan.c                # Compile the generated C code
./pan                          # Execute the model checker
```

### Model Explanation

- **TrafficMonitor Process**: Checks for invariant violations by monitoring the signals of each direction. If it detects conflicting signals, it triggers an assertion failure.
  
- **Traffic Light Processes**: Each direction (North, South, East, West) has a corresponding traffic light process that can switch between `PROCEED` and `DANGER` states based on incoming signals.

- **CentralControl Process**: Alternates the traffic signals between North-South and East-West every cycle, ensuring that at least one direction has a green light at all times.

### Properties Verification

- **Safety Constraints**: The system verifies that it never allows conflicting signals in both North-South and East-West directions.

- **Response Properties**: Ensures that when a signal turns `PROCEED`, it will eventually turn to `DANGER`.

## Usage Example

Once you have the SPIN model set up and running, you can observe the outputs indicating the status of traffic lights and any potential invariant violations detected by the `TrafficMonitor`.

Example output:

```
North Traffic Light: Switched to PROCEED
South Traffic Light: Switched to PROCEED
East Traffic Light: Switched to DANGER
West Traffic Light: Switched to DANGER
Invariant violation: Conflicting traffic signals detected!
```

## License

This project is licensed under the MIT License.

## Contributors

- [Oscar Oguledo](https://github.com/oscaroguledo)

Feel free to open an issue or submit a pull request if you'd like to contribute!

---

You can make any additional changes or let me know if there's anything else you need!
