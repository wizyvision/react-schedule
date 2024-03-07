import React from 'react';
import PropTypes from 'prop-types';

const SlotBackgroundPropTypes = PropTypes.shape({
     /**
     * set background of drop, when the appointment can be drop in the slot
     */
    dropBg: PropTypes.string,
     /**
     * set background of drop, when the appointment is over the slot
     */
    overBg: PropTypes.string
})

export const SlotPropTypes = PropTypes.shape({
     /**
     * Set the primary duration - Primary Duration is the duration in header of the scheduler
     * @default 60
     */
    primaryDuration: PropTypes.number,
     /**
     * Set the secondary duration, Secondary Duration is the duration inside each Primary Duration
     * @default 30
     */
    secondaryDuration: PropTypes.number,
     /**
     * colSpan should be set accordingly to secondaryDuration
     * @default 2
     */
    colSpan: PropTypes.number,
     /**
     * component is used to wrapped the whole scheduler
     */
    component: PropTypes.node,
     /**
     * Override the style
     */
    style: PropTypes.object, 
     /**
     * Override the slot background when it is to be dropped or its just over the slot
     */
    slotBackground: SlotBackgroundPropTypes
});


export const SlotDefaultValues = {
    primaryDuration: 60,
    secondaryDuration: 30,
    colSpan: 2,
    component: <div />,
    style: PropTypes.object, 
    slotBackground: {
        dropBg: undefined,
        overBg: undefined
    }
}