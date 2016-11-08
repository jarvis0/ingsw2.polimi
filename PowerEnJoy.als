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
	all c: Car, n: Notification | n in c.notifications <=> c = n.car

	// each redistribution needed notification is related to exactly one car
	all c: Car, r: CarsRedistributionNeeded | c.redistributionNeeded = r and r.car = c

	//each car has different positions
	all c1, c2: Car | c1 != c2 implies c1.position != c2.position

	//no latitude and langitude without position and no position with the same latitude and longitude
	all lat: LatitudePosition, lon: LongitudePosition | (one p: Position | p.latitude = lat and p.longitude = lon)

	//no user cannot have personal information and no user with the same personal information
	all personalInfo: PersonalInformation | (one u: User | u.personalInformation = personalInfo)

	//no user cannot have payment information***************
	all paymentInfo: PaymentInformation | (one u: User | u.paymentInformation = paymentInfo)

	//no users with the same username
	all p1, p2: PersonalInformation | p1 != p2 implies p1.username != p2.username

	//no ride without reservation and no ride of the same reservation
	all r: Ride | (one res: Reservation | res.ride = r)

	//no reservation for the same car
	all r1, r2: Reservation | r1 != r2 implies r1.car != r2.car

	//no reservation for issued cars
	all r: Reservation | (no r.car.notifications & (TechicalIssue + AlmostEmptyBatteryIssue))

	#Reservation > 0
	#Position > 0
	#Text >= 2
}

sig Position {
	latitude: LatitudePosition,
	longitude: LongitudePosition
}

sig User {
	pendingInformation: Bool,
	personalInformation: PersonalInformation,
	paymentInformation: PaymentInformation,
	reservations: Reservation
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
//	reservationTime: Time,
//	doorsUnlockTime: lone Time,
	passengersNumber: Int,
	car: Car,
	ride: lone Ride
} {
	passengersNumber >= 1 and passengersNumber <= 5
}

sig Ride {
	//doorsLockTime: Time,
	//engineStartTime: Time
}

pred show {
}

run show for 4
