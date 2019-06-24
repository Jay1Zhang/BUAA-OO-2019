//package com.oocourse.elevator1;

import com.oocourse.elevator1.ElevatorInput;
import com.oocourse.elevator1.PersonRequest;

class TestInputInterface {
    public static void main(String[] args) throws Exception {
        ElevatorInput elevatorInput = new ElevatorInput(System.in);
        while (true) {
            PersonRequest request = elevatorInput.nextPersonRequest();
            // when request == null
            // it means there are no more lines in stdin
            if (request == null) {
                break;
            } else {
                // a new valid request
                System.out.println(request);
            }
        }
        elevatorInput.close();
    }
}