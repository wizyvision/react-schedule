import React from 'react';
import moment from 'moment';

import {
  getAppointmentWidth,
  getAppointmentHeight,
} from '../../utils/getAppointmentStyle';

import AppointmentItem from './AppointmentItem';

function Appointments(props) {
  const { appointments, timeSlot, secondaryDuration } = props;
  return (
    appointments &&
    appointments?.map((appointment) => {
      const startDate = moment(appointment.schedule.startDate);
      const endDate = moment(appointment.schedule.endDate);
      const height = getAppointmentHeight(appointment.height);

      return (
        <AppointmentItem
          key={appointment.id}
          appointment={appointment}
          width={getAppointmentWidth(
            timeSlot,
            startDate,
            endDate,
            secondaryDuration
          )}
          height={height}
        />
      );
    })
  );
}

export default Appointments;
