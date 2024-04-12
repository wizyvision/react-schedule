import moment from 'moment';

export function getSortAppointments (appointments, user){
  return appointments.filter(
    (event) => user === event.user).sort(
    (a, b) => a.schedule?.startDate - b.schedule?.startDate)
}

export function getFilteredAppointments(
  appointmentList,
  user,
  timeSlot,
  date,
  duration,
  concurrentMapping
) {
  return appointmentList
    .filter((appointment) => appointment.user === user)
    .filter((appointment) => {
      const startDate = moment(appointment.schedule?.startDate);

      const currentDate = moment(date);
      const slotStartTime = moment(
        `${currentDate.format('YYYY-MM-DD')} ${timeSlot}`,
        'YYYY-MM-DD hh:mm a'
      );
      const slotEndTime = moment(slotStartTime).add(duration, 'minutes');

      return (
        startDate.isSame(currentDate, 'day') &&
        (startDate.isAfter(slotStartTime) || slotStartTime.isSame(startDate)) &&
        startDate.isBefore(slotEndTime)
      );
    })
    .map((appointment) => {
      const height = concurrentMapping[appointment.id]
      return {
        ...appointment,
        height,
      };
    });
}

export const getUpdatedAppointments = (
  appointments,
  appointment,
  date,
  timeSlot,
  duration,
  user
) => {
  const slotDate =  moment(date, 'ddd MMM DD YYYY HH:mm:ss [GMT]ZZ').format('YYYY-MM-DD') + ' ' + timeSlot;
  const slotStartTime = moment(slotDate);

  const existingIndex = appointments.findIndex(
    (existingAppointment) => existingAppointment.id === appointment.id
  );

  let updatedAppointments = {
    ...appointment,
    user,
    schedule: {
      startDate: slotStartTime.toDate(),
      endDate: moment(slotStartTime).add(duration, 'minutes').toDate(),
    },
  };
  if (existingIndex !== -1) {
    updatedAppointments = {
      ...appointment,
      user,
      schedule: {
        startDate: slotStartTime.toDate(),
        endDate: moment(slotStartTime)
          .add(
            moment(appointment.schedule.endDate).diff(
              moment(appointment.schedule.startDate),
              'minutes'
            ), // Keep the original duration
            'minutes'
          )
          .toDate(),
      },
    };
  }
  return updatedAppointments;
};

export const getAppointmentDuration = (schedule) => {
  const startDate = moment(schedule.startDate)
  const endDate = moment(schedule.endDate)
  const duration = moment.duration(endDate.diff(startDate));
  
  if (duration.asHours() < 1) {
    return duration.asMinutes() + ' minutes';
  } else {
    return duration.asHours() + ' hours';
  }
}