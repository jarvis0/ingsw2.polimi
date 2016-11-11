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
	cumulativeNotifications: set CumulativeNotification,
	almostEmptyBattery: lone AlmostEmptyBatteryIssue,
	redistributionNeeded: lone CarsRedistributionNeeded
}

abstract sig Notification {
	car: Car
}

abstract sig CumulativeNotification extends Notification {
}

sig TechnicalIssue extends CumulativeNotification {
}

sig MinorIssue extends CumulativeNotification {
}

sig AlmostEmptyBatteryIssue extends Notification {
}

sig CarsRedistributionNeeded extends Notification {
}

fact {

	//each notification is related to the corresponding car and the car has the set of his notifications
	all c: Car, n: CumulativeNotification | (n in c.cumulativeNotifications and c = n.car) or (n not in c.cumulativeNotifications and c != n.car)

	//each almost empty battery issue is related to the corresponding car and the car has his almost empty battery issue
	all c: Car, empty: AlmostEmptyBatteryIssue | (c.almostEmptyBattery = empty and empty.car = c) or (c.almostEmptyBattery != empty and empty.car != c)

	all c: Car, r: CarsRedistributionNeeded | (c.redistributionNeeded = r and r.car = c) or (c.redistributionNeeded != r and r.car != c)

	// each redistribution needed notification is related to exactly one car
//	all c: Car, r: CarsRedistributionNeeded | c.redistributionNeeded = r and r.car = c

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
//	all r: Reservation | ((no (r.car.cumulativeNotifications & TechnicalIssue))/* and (r.car.almostEmptyBattery not in AlmostEmptyBatteryIssue)*/)

	//no reservation without user and no user with the same active reservation
	all r: Reservation | (one u: User | r = u.activeReservation)

	//riding cars are at the same position of the driver
	all ri: Ride | (one r: Reservation | (one u: User | (r = u.activeReservation and r.car.position = u.position and r.ride = ri)))

	//a car which is not in a ride cannot be out of a safe parking area
//	all r: Reservation | (one p: SafeParkingArea | no r.ride implies r.car.position = p.position)

	#Car > 3
	#CarsRedistributionNeeded > 1
	#CumulativeNotification > 1
	#AlmostEmptyBatteryIssue > 1
	#Position > 0
	#Text >= 2
}

assert noSameAlmostEmptyBatteryIssues {
	all c1, c2: Car | c1 != c2 <=> c1.almostEmptyBattery != c2.almostEmptyBattery
}
//check noSameAlmostEmptyBatteryIssues

assert noSameRedistributionNeededIssues {
	all c1, c2: Car | c1 != c2 <=> c1.redistributionNeeded != c2.redistributionNeeded
}
//check noSameRedistributionNeededIssues

assert noSameCumulativeNotifications {
	all c1, c2: Car | c1 != c2 <=> no c1.cumulativeNotifications & c2.cumulativeNotifications
}
//check noSameCumulativeNotifications

assert noUsersWithSameUsername {
	all p1, p2: PersonalInformation | p1 != p2 <=> p1.username != p2.username
}
//check noUsersWithSameUsername

assert noCarsWithSamePosition {
	all c1, c2: Car | c1 != c2 <=> c1.position != c2.position
}
//check noCarsWithSamePosition

assert noReservationForSameCars {
	all r1, r2: Reservation | r1 != r2 <=> r1.car != r2.car
}
//check noReservationForSameCars

assert noRideIffUserAndCarAtSamePosition {
	all u: User | (lone r: Reservation | (lone ri: Ride | (r = u.activeReservation and r.car.position = u.position <=> r.ride = ri)))
}
//check noRideIffUserAndCarAtSamePosition

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

run show for 6
