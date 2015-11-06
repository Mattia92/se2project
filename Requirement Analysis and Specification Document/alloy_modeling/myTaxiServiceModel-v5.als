/*************** CLASSES ***************/

sig Queue { 
	first: one AvailableTaxiDriver,
	cityArea : one Location 
}

abstract sig TaxiDriver {}

sig AvailableTaxiDriver extends TaxiDriver {
	next: lone AvailableTaxiDriver
}

sig BusyTaxiDriver extends TaxiDriver {}

sig Passenger {} 

sig Ride {
	driver : one BusyTaxiDriver,
	passenger : some Passenger,
	origin : one Location,
	destination : one Location

} {
	#passenger < 4 && 
	#passenger > 1 &&
	origin != destination // <------- Be careful!
}

sig Location {}
	

	

/*************** CONSTRAINTS ***************/

// ensures that no taxi driver is the subsequent of himself inside a queue
fact nextNotReflexive { no n:TaxiDriver | n = n.next }

// ensures that each taxi driver is associated to only one queue
fact onlyOneQueuePerAvailableTaxiDriver {
	all d:AvailableTaxiDriver | one q:Queue | d in q.first.*next 
}

// ensures that the last taxi driver of the queue exists and is unique
fact notCyclicQueue { 
	no d:TaxiDriver | d in d.^next 
}

// ensures that all taxi drivers marked as busy are making only one ride
fact AllBusyTaxiDriverAreInARide {
	all d:BusyTaxiDriver | one r:Ride | r.driver = d
}

// ensures that all passengers in a ride are in only one ride
fact OnlyOneRidePerTimePerPassenger {
	all disj r1, r2:Ride | disj[r1.passenger, r2.passenger]
}

/*************** ASSERTIONS ***************/

// check that every taxi driver belong to one queue only
assert UniqueQueuePerTaxiDriver {
	no disj q1, q2:Queue | one d:AvailableTaxiDriver | (d in q1.first.*next and d in q2.first.*next)
}
check UniqueQueuePerTaxiDriver

// check that every busy taxi driver is making only one ride
assert OnlyOneRidePerTaxiDriver {
	no disj r1, r2 : Ride | r1.driver != r2.driver
}
check OnlyOneRidePerTaxiDriver

// check that every passenger in a ride is in only one ride
assert OnlyOneRidePerPassenger {
	no disj r1, r2 : Ride | not disj[r1.passenger, r2.passenger]
}
check OnlyOneRidePerPassenger


/*************** PREDICATES ***************/
pred show() {}

run show for 7

pred showRides() {
	#Passenger>4
}

run showRides for 7 but exactly 2 Ride
