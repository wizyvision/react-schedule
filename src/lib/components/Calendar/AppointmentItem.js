import React from 'react';
import { useDrag } from 'react-dnd';
import { Typography, darken } from '@mui/material';

import AppointmentContainer from '../../container/Appointment';

function AppointmentItem(props) {
  const { appointment, width, height } = props;

  const [{ isDragging }, drag] = useDrag({
    type: 'APPOINTMENT',
    item: { appointment },
    collect: (monitor) => ({
      isDragging: !!monitor.isDragging(),
    }),
  });

  const color = appointment.user.color;

  return (
    <AppointmentContainer
      key={appointment.id}
      ref={drag}
      isDragging={isDragging}
      height={height}
      width={width}
      appointmentColor={color}
    >
      <div
        style={{
          padding: 4,
        }}
      >
        <Typography sx={{ color: darken(color, 0.5) }}>
          {appointment.title}
        </Typography>
      </div>
    </AppointmentContainer>
  );
}

export default AppointmentItem;
