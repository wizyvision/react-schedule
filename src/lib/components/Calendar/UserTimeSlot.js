import React from 'react';
// import { useDrop } from 'react-dnd';
import moment from 'moment';

import { getFilteredAppointments,getSortAppointments, getUpdatedAppointments } from '../../utils/getAppointments';
import { getSlotWidth } from '../../utils/getAppointmentStyle';

import { useSchedulerContext } from '../../context/SchedulerProvider';
import Slot from '../../container/Slot';


function UserTimeSlot(props) {
  const { user, timeSlot, index } = props;
  

  const { appointmentList, onAppointmentChange, duration, date, SlotProps } =
    useSchedulerContext();
  const { secondaryDuration = 30 } = SlotProps || {};

//   const [{ isOver, canDrop }, drop] = useDrop({
//     accept: 'APPOINTMENT',
//     drop: (appointment, monitor) => {
//       const droppedAppointment = appointment.appointment;
//       const updatedAppointments = getUpdatedAppointments(
//         appointmentList,
//         droppedAppointment,
//         date,
//         timeSlot,
//         duration,
//         user
//       );
//       onAppointmentChange(updatedAppointments);
//     },
//     collect: (monitor) => ({
//       isOver: monitor.isOver(),
//       canDrop: monitor.canDrop(),
//     }),
//   });

//   const sortedAppointments = getSortAppointments(appointmentList, user);
//   const concurrentAppointments = {};
//   let previousConcurrentCount = 0;
//   sortedAppointments.forEach((event, index) => {
//     const startDate = moment(event.schedule.startDate);
//     const count = sortedAppointments.reduce((acc, otherEvent, otherIndex) => {
//       if (
//         index !== otherIndex &&
//         moment(otherEvent.schedule.startDate).isBefore(startDate) &&
//         moment(otherEvent.schedule.endDate).isAfter(startDate)
//       ) {
//         return acc + 1;
//       }
//       return acc;
//     }, 0);
//     concurrentAppointments[event.id] =
//       count > 0 ? count + previousConcurrentCount : 0;
//     // Update previousConcurrentCount for the next event
//     previousConcurrentCount = count > 0 ? concurrentAppointments[event.id] : 0;
//   });

//   const filteredAppointments = getFilteredAppointments(
//     appointmentList,
//     user,
//     timeSlot,
//     date,
//     secondaryDuration,
//     concurrentAppointments
//   );

//   const width = getSlotWidth(secondaryDuration);

  return (
    <Slot
      colSpan={1}
    //   ref={drop}
      index={index}
    //   canDrop={canDrop}
    //   isOver={isOver}
    //   width={width}
    >
      {/* <div style={{ overflow: 'visible', width: width }}>
        <FilteredAppointments
          appointments={filteredAppointments}
          secondaryDuration={secondaryDuration}
          timeSlot={timeSlot}
        />
      </div> */}
    </Slot>
  );
}

export default UserTimeSlot;
