open util/boolean
open util/ordering[Time] as times

sig Text {
}

sig LatitudePosition {
}

sig LongitudePosition {
}

sig Time {
}

sig Car {
	available: Bool,
	position: Position,
	charging: Bool,
	notifications: set Notification,
	redistributionNeeded: lone CarsRedistributionNeeded
}

abstract sig Notification {
	car: Car
}

sig MinorIssue extends Notification {
}

sig AlmostEmptyBatteryIssue extends Notification {
}

sig TechicalIssue extends Notification {
}

sig CarsRedistributionNeeded {
	car: Car
}

fact {

	//each notification is related to the corresponding car and a car has the set of his notifications
	all c: Car, n: Notification | n in c.notifications and c = n.car

	// each redistribution needed notification is related to exactly one car
	all c: Car, r: CarsRedistributionNeeded | c.redistributionNeeded = r and r.car = c

	//no car with same position
	no c1, c2: Car | c1 != c2 and c1.position = c2.position

	//no latitude and langitude without position and no position with the same latitude and longitude
	all lat: LatitudePosition, lon: LongitudePosition | (one p: Position | p.latitude = lat and p.longitude = lon)

	//no user cannot have personal information and no user with the same personal information
	all personalInfo: PersonalInformation | (one u: User | u.personalInformation = personalInfo)

	//no user cannot have payment information*************** some <> one
	all paymentInfo: PaymentInformation | (one u: User | u.paymentInformation = paymentInfo)

	//no users with the same username
	no p1, p2: PersonalInformation | p1 != p2 and p1.username = p2.username

	//no ride without reservation and no ride of the same reservation
	all r: Ride | (one res: Reservation | res.ride = r)

	//two reservations have different car
	no r1, r2: Reservation, c: Car | r1 != r2 and r1.car = c and r2.car = c

	//no reservation for issued cars
	all r: Reservation | (no r.car.notifications & (TechicalIssue + AlmostEmptyBatteryIssue))

	//no reservation without user and no user with the same active reservation
	all r: Reservation | (one u: User | r = u.activeReservation)

	//riding cars are at the same position of the driver
	all ri: Ride | (one r: Reservation | (one u: User | (r = u.activeReservation and r.car.position = u.position and r.ride = ri)))

	//a car which is not in a ride cannot be out of a safe parking area
//	all r: Reservation | (one p: SafeParkingArea | no r.ride implies r.car.position = p.position)

	#Reservation > 0
	#Position > 0
	#Text >= 2
}

/*
assert noUsersWithSameUsername {
	all p1, p2: PersonalInformation | p1 != p2 <=> p1.username != p2.username
}
check noUsersWithSameUsername

assert noCarsWithSamePosition {
	all c1, c2: Car | c1 != c2 <=> c1.position != c2.position
}
check noCarsWithSamePosition

assert noReservationForSameCars {
	all r1, r2: Reservation | r1 != r2 <=> r1.car != r2.car
}
check noReservationForSameCars

/*assert noRideIffUserAndCarAtSamePosition {
	all u: User | (lone r: Reservation | (lone ri: Ride | (r = u.activeReservation and r.car.position = u.position <=> r.ride = ri)))
}
check noRideIffUserAndCarAtSamePosition*/

sig Position {
	latitude: LatitudePosition,
	longitude: LongitudePosition
}

sig User {
	position: Position,
	pendingInformation: Bool,
	personalInformation: PersonalInformation,
	paymentInformation: PaymentInformation,
	activeReservation: lone Reservation
}

sig PersonalInformation {
	username: Text,
	password: Text,
} {
	username != password
}

sig PaymentInformation {
}

sig Reservation {
	car: Car,
	ride: lone Ride
}

sig Ride {
	passengersNumber: Int,
} {
	passengersNumber >= 1 and passengersNumber <= 5
}

/*sig SafeParkingArea {
	position: Position,
	car: set Car
}*/

pred show {
}

run show for 4
